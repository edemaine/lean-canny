/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalNormalSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightCoefficientSpace
public import LeanCanny.Algebra.FixedWidthMonomialSpace
/-! # Current-bank normal monomials over an external full-row packet -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalNormalAtBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedOldHeightBits (state)
open IntegralMixedFramedPhysicalHeightBits (Active)
open IntegralMixedPhysicalDenominatorPostBits (rawScaleReader scale scaleAt multiply multiply_FP multiply_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family rawScaleReader multiply BinaryNat.mulMod
  IntegralMixedFramedPhysicalAffineBits.common scale IntegralCriticalHistoryTask.modulus

noncomputable def integer (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (p : List Bool) : ℤ :=
  if Active P (base p) then IntegralMixedHistory.commonDenominator (state P D J (base p))*
    scale P (IntegralMixedFramedPhysicalBits.family P D J) (base p) (selected p) else 0

noncomputable def product (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (p : List Bool) :=
  multiply P (pair (base p) (pair (IntegralMixedFramedPhysicalAffineBits.common P a D J c (base p))
    (rawScaleReader P (IntegralMixedFramedPhysicalBits.family P D J) (pair (base p) (BinaryNatCode.encode (selected p))))))

noncomputable def value (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (p : List Bool) := if Active P (base p) then product P a D J c base selected p else []

attribute [local irreducible] product value

theorem product_space (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ) (hs : BinaryFn selected) :
    SpaceFunction (product P a D J c base selected) := by
  have EQ:=(IntegralMixedFramedPhysicalAffineBits.common_space P a D J c hc).precompose base hb
  have ES:=c.scalar.physicalScales.precompose (fun p=>pair (base p) (BinaryNatCode.encode (selected p))) (mem_FP_pair hb hs.bits_mem_FP)
  have EP : (fun z=>pair (base (pairFst z)) (pairSnd z))∈FP :=mem_FP_pair (mem_FP_comp pairFst_mem_FP hb) pairSnd_mem_FP
  have HE:=(EQ.pairOutputs ES).withInput.postcompose (multiply P∘fun z=>pair (base (pairFst z)) (pairSnd z))
    (mem_FP_comp EP (multiply_FP P a))
  exact HE.congr (funext fun p=>by
    unfold product
    simp only [Function.comp_apply,pairFst_pair,pairSnd_pair])

theorem value_space (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ) (hs : BinaryFn selected) :
    SpaceFunction (value P a D J c base selected) := by
  have E:=SpaceFunction.branch (fun p=>decide (Active P (base p)))
    ((IntegralMixedFramedPhysicalHeightBits.active_FP P a).comp hb).flag_mem_FP
    (product_space P a D J c hc base hb selected hs) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun _=>by unfold value; simp only [decide_eq_true_eq])

theorem value_actual (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (selected : List Bool→ℕ) (p : List Bool) :
    value P a D J c base selected p=residueBits (integer P D J base selected p : ZMod (modulus P (base p))) := by
  unfold value integer
  by_cases ha : Active P (base p)
  · rw [ite_eq_left ha,ite_eq_left ha]
    unfold product
    rw [IntegralMixedFramedPhysicalAffineBits.common_actual_at P a D J c (base p) ha.1 (by rw [ha.2];omega),
      IntegralMixedPhysicalDenominatorPostBits.rawScaleReader_packet,multiply_packet]
    rw [Int.cast_mul]
    rfl
  · rw [ite_eq_right ha,ite_eq_right ha]
    simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem monomial_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ) (hs : BinaryFn selected)
    (N W coordinate power : List Bool→ℕ) (target : List Bool→List Bool)
    (hN : UnaryFn N) (hW : UnaryFn W) (hcoordinate : BinaryFn coordinate) (hpower : BinaryFn power) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value N W
      (FixedWidthMonomialBits.polynomial N coordinate power (integer P D J base selected)) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HR : ∀p,value P a D J c base selected p=residueBits
      (integer P D J base selected p : ZMod (Nat.fromBitsLE (IntegralMixedFramedPhysicalHeightBits.modulusWord P (base p))+1)) := by
    intro p
    exact (value_actual P a D J c base selected p).trans
      (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl
        (IntegralMixedFramedPhysicalHeightBits.modulusWord_value P (base p)).symm)
  exact FixedWidthMonomialBits.coefficient_evaluator N W coordinate power target _ _ _
    (value_space P a D J c hc base hb selected hs) HR hN hW hcoordinate hpower ht

end LeanCanny.Algebra.IntegralMixedFramedPhysicalNormalAtBits
