/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldBankCofactor
public import LeanCanny.Algebra.IntegralMixedVirtualDenominatorValue
public import LeanCanny.Algebra.IntegralMixedDenominatorRecurrence
public import LeanCanny.Algebra.ModularProductSpace
/-! # Original affine scales turn the bank product into the actual denominator

Only original integer rule-scale cells are charged primitive reads. The
old retained-bank product arrives as a recursive-controller accumulator.
No evaluator for that product or for an interpreted leading is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualDenominatorPostBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.mulMod BinaryNat.powMod modulus

noncomputable def arity (P : Parameters) (F : Family) (q : List Bool) := F.ambient (IntegralMixedVirtualTaskBits.saved P q) + 1
noncomputable def scale (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) : ℤ :=
  if hi : i < arity P F q then (F.rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales ⟨i, hi⟩ else 1
noncomputable def scaleAt (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) : ZMod (modulus P q) := scale P F q i
noncomputable def rawScaleReader (P : Parameters) (F : Family) (z : List Bool) :=
  residueBits (scaleAt P F (pairFst z) (Nat.fromBitsLE (pairSnd z)))
noncomputable def ruleProduct (P : Parameters) (F : Family) (q : List Bool) :=
  residueBits ((∏ i, (F.rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales i : ℤ) : ZMod (modulus P q))

theorem arity_unary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : UnaryFn (arity P F) :=
  (h.ambient.comp (IntegralMixedVirtualTaskBits.saved_FP P a)).add (UnaryFn.const 1)

theorem rawScaleReader_packet (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) :
    rawScaleReader P F (pair q (BinaryNatCode.encode i)) = residueBits (scaleAt P F q i) := by
  unfold rawScaleReader
  rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem ruleProduct_space (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (hr : SpaceFunction (rawScaleReader P F)) : SpaceFunction (ruleProduct P F) := by
  have E := ModularProduct.evaluatorWithModulus hr
    (fun q => BinaryNatCode.encode (arity P F q)) (fun q => BinaryNatCode.encode (modulus P q))
    (BinaryFn.ofUnary (arity_unary P a F h)).bits_mem_FP (modulus_binary P a).bits_mem_FP
    (modulus P) (funext fun _ => Nat.fromBitsLE_bits _) (scaleAt P F)
    (fun q => Nat.pos_of_ne_zero (modulus_ne_zero P q)) (fun q j _ => rawScaleReader_packet P F q j)
  refine E.congr (funext fun q => ?_)
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold ruleProduct
  rw [Int.cast_prod, Finset.prod_range]
  apply congrArg residueBits
  apply Finset.prod_congr rfl
  intro i _
  unfold scaleAt scale
  rw [dite_eq_left i.isLt]
  rfl

noncomputable def power (P : Parameters) (F : Family) (z : List Bool) :=
  BinaryNat.powMod (pair (pairSnd z) (pair (BinaryNatCode.encode (arity P F (pairFst z))) (BinaryNatCode.encode (modulus P (pairFst z) - 1))))
def multiply (P : Parameters) (z : List Bool) :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))

theorem power_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : power P F ∈ FP := by
  unfold power
  have HA : BinaryFn (fun z => arity P F (pairFst z)) := (BinaryFn.ofUnary (arity_unary P a F h)).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z) - 1) := ((modulus_binary P a).sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_pair HA.bits_mem_FP HM.bits_mem_FP)) BinaryNat.powMod_mem_FP

theorem multiply_FP (P : Parameters) (a : Access P) : multiply P ∈ FP := by
  unfold multiply
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

noncomputable def post (P : Parameters) (F : Family) (z : List Bool) :=
  multiply P (pair (pairFst z) (pair (ruleProduct P F (pairFst z)) (power P F z)))

theorem post_space (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (hr : SpaceFunction (rawScaleReader P F)) : SpaceFunction (post P F) := by
  unfold post
  have ER := (ruleProduct_space P a F h hr).precompose pairFst pairFst_mem_FP
  have EP := SpaceFunction.ofFP _ (power_FP P a F h)
  exact ((SpaceFunction.ofFP _ pairFst_mem_FP).pairOutputs (ER.pairOutputs EP)).postcompose (multiply P) (multiply_FP P a)

theorem power_packet (P : Parameters) (F : Family) (q : List Bool) (x : ZMod (modulus P q)) :
    power P F (pair q (residueBits x)) = residueBits (x ^ arity P F q) := by
  simp only [power, pairFst_pair, pairSnd_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (modulus_ne_zero P q) x

theorem multiply_packet (P : Parameters) (q : List Bool) (x y : ZMod (modulus P q)) :
    multiply P (pair q (pair (residueBits x) (residueBits y))) = residueBits (x * y) := by
  simp only [multiply, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem post_packet (P : Parameters) (F : Family) (q : List Bool) (x : ZMod (modulus P q)) :
    post P F (pair q (residueBits x)) = residueBits
      (((∏ i, (F.rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales i : ℤ) : ZMod (modulus P q)) * x ^ arity P F q) := by
  unfold post
  simp only [pairFst_pair]
  rw [power_packet]
  unfold ruleProduct
  rw [multiply_packet]

theorem post_full (P : Parameters) (F : Family) (q : List Bool) :
    post P F (pair q (IntegralMixedOldBankCofactorBits.value P F (IntegralMixedOldBankCofactorBits.count P F) q)) =
      IntegralMixedVirtualDenominatorBits.value P F q := by
  rw [IntegralMixedOldBankCofactorBits.value_full, post_packet]
  rw [IntegralMixedVirtualDenominatorBits.snapshot]
  change residueBits _ = residueBits (IntegralMixedVirtualSweepSource.denominator F (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q))
  unfold IntegralMixedVirtualSweepSource.denominator
  rw [IntegralMixedDenominatorBits.common_scales]
  simp only [Int.cast_mul, Int.cast_pow]
  congr 1
  exact mul_comm _ _
end LeanCanny.Algebra.IntegralMixedVirtualDenominatorPostBits
