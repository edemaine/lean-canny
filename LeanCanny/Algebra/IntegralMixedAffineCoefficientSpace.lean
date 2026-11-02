/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineCode
/-! # Native space access to affine coefficients from encoded original terms -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineCode
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Algebra.RationalSubstitution.Indexed
open scoped Classical

def zeroTarget (N : List Bool → ℕ) (c : List Bool) := FixedWidthNatVector.encode (N c) 1 (fun _ => 0)
def unitTarget (N J : List Bool → ℕ) (c : List Bool) := FixedWidthNatVector.encode (N c) 1 (fun j => if j = J c then 1 else 0)

theorem zeroTarget_FP (N : List Bool → ℕ) (hN : UnaryFn N) : zeroTarget N ∈ FP := by
  apply FixedWidthNatVector.encode_mem_FP N (fun _ => 1) (fun _ _ => 0) hN (UnaryFn.const 1) (fun _ => []) (constFn_mem_FP [])
  intro c i
  rfl

theorem unitTarget_FP (N J : List Bool → ℕ) (hN : UnaryFn N) (hJ : BinaryFn J) : unitTarget N J ∈ FP := by
  let reader := fun z : List Bool => if Nat.fromBitsLE (pairSnd z) = J (pairFst z) then [true] else []
  have HR : reader ∈ FP := ((BinaryFn.fromBits pairSnd_mem_FP).eq (hJ.comp pairFst_mem_FP)).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])
  apply FixedWidthNatVector.encode_mem_FP N (fun _ => 1) (fun c j => if j = J c then 1 else 0) hN (UnaryFn.const 1) reader HR
  intro c i
  simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> rfl

theorem zero_exponent (N : List Bool → ℕ) (c : List Bool) :
    exponentVector (N c) (FixedWidthQuery.coordinate (fun _ => 1) (zeroTarget N) c) = 0 := by
  ext j
  change Nat.fromBitsLE (((zeroTarget N c).drop (j.val * 1)).take 1) = 0
  exact FixedWidthNatVector.decode_block (N c) 1 (fun _ => 0) j.val j.isLt (by decide)

theorem unit_exponent (N J : List Bool → ℕ) (c : List Bool) (hi : J c < N c) :
    exponentVector (N c) (FixedWidthQuery.coordinate (fun _ => 1) (unitTarget N J) c) =
      Finsupp.single (⟨J c, hi⟩ : Fin (N c)) 1 := by
  ext j
  have H := FixedWidthNatVector.decode_block (N c) 1 (fun j => if j = J c then 1 else 0)
    j.val j.isLt (by split_ifs <;> decide)
  change Nat.fromBitsLE (((unitTarget N J c).drop (j.val * 1)).take 1) = _
  unfold unitTarget
  rw [H]
  simp only [Finsupp.single_apply, Fin.ext_iff, eq_comm]

theorem constant_space (E : List Bool → IntegralMixedHistory.AffineExpr) (source mod : List Bool → List Bool)
    (hs : source ∈ FP) (hm : mod ∈ FP) (he : ∀ c, source c = encode (E c)) :
    SpaceFunction (fun c => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (E c) : ZMod (Nat.fromBitsLE (mod c) + 1))) := by
  let N := ETR.CollectedCoefficient.dimension source
  have HN : UnaryFn N := ETR.CollectedCoefficient.dimension_unary hs
  have HV := ETR.SizedCollectedCoefficient.evaluator HN (UnaryFn.const 1) hs (zeroTarget_FP N HN) hm
    (ETR.CollectedCoefficient.arity_le_dimension source)
  apply HV.congr
  funext c
  unfold ETR.SizedCollectedCoefficient.value
  rw [zero_exponent, he c, encode, ETR.TermView.term_toBits, constant_coefficient]

theorem reference_space (E : List Bool → IntegralMixedHistory.AffineExpr) (source mod : List Bool → List Bool)
    (J : List Bool → ℕ) (hs : source ∈ FP) (hm : mod ∈ FP) (hJ : BinaryFn J)
    (he : ∀ c, source c = encode (E c)) :
    SpaceFunction (fun c => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (E c) (J c) : ZMod (Nat.fromBitsLE (mod c) + 1))) := by
  let N := ETR.CollectedCoefficient.dimension source
  have HN : UnaryFn N := ETR.CollectedCoefficient.dimension_unary hs
  have HV := ETR.SizedCollectedCoefficient.evaluator HN (UnaryFn.const 1) hs (unitTarget_FP N J HN hJ) hm
    (ETR.CollectedCoefficient.arity_le_dimension source)
  have HP := hJ.lt (BinaryFn.ofUnary HN)
  have HB := SpaceFunction.branch (fun c => decide (J c < N c)) HP.flag_mem_FP HV (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply HB.congr
  funext c
  by_cases hi : J c < N c
  · rw [ite_eq_left (decide_eq_true hi)]
    unfold ETR.SizedCollectedCoefficient.value
    rw [unit_exponent N J c hi, he c, encode, ETR.TermView.term_toBits, reference_coefficient]
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hi)]
    have HA := ETR.CollectedCoefficient.arity_le_dimension source c
    rw [he c, encode, ETR.TermView.term_toBits] at HA
    rw [reference_outside (E c) (N c) (J c) HA (by omega)]
    exact ArithmeticBits.zero_residueBits _
end LeanCanny.Algebra.IntegralMixedAffineCode
