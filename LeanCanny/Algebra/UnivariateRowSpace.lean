/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DiagonalUnivariateSystem
public import LeanCanny.Algebra.FixedWidthRowArithmetic
public import LeanCanny.Algebra.PrimitivePairReaders

/-! # Native coefficients of a univariate polynomial in a selected coordinate -/

@[expose] public section
namespace LeanCanny.Algebra.UnivariateRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

lemma entry_eq_coordinate (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    FixedWidthPolynomial.entry (W c) (Nat.fromBitsLE (target c)) i = FixedWidthQuery.coordinate W target c i := by
  unfold FixedWidthQuery.coordinate
  rw [FixedWidthPolynomial.entry_eq_digit, BinaryNat.value_take, FixedWidthPolynomial.drop_value]

def Supported (A W : List Bool → ℕ) (i : (c : List Bool) → Fin (A c))
    (target : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ j < A c, j = (i c).val ∨ FixedWidthQuery.coordinate W target c j = 0

theorem supported_FP {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    (i : (c : List Bool) → Fin (A c)) (hi : UnaryFn (fun c => (i c).val))
    {target : List Bool → List Bool} (ht : target ∈ FP) : FPPred (Supported A W i target) := by
  have hw := hW.lift
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hw)) hw
  have hj := FPPred.eq UnaryFn.index (hi.comp pairFst_mem_FP)
  have hz := BinaryNat.eq_const_fppred hs 0
  apply (FPPred.forall_lt hA (hj.or hz)).of_iff
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, Supported, FixedWidthQuery.coordinate]
  have he (j : ℕ) : (i (pairFst (pair c (List.replicate j true)))).val = (i c).val :=
    congrArg (fun u => (i u).val) (pairFst_pair c (List.replicate j true))
  simp only [he]

lemma supported_iff (A W : List Bool → ℕ) (i : (c : List Bool) → Fin (A c))
    (target : List Bool → List Bool) (c : List Bool) :
    Supported A W i target c ↔ ∀ j : Fin (A c), j ≠ i c →
      FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c)) j = 0 := by
  simp only [Supported, FixedWidthPolynomial.nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    entry_eq_coordinate]
  constructor
  · intro h j hj
    rcases h j.val j.isLt with he | he
    · exact False.elim (hj (Fin.ext he))
    · exact he
  · intro h j hj
    by_cases he : j = (i c).val
    · exact Or.inl he
    · exact Or.inr (h ⟨j, hj⟩ (fun H => he (congrArg Fin.val H)))

theorem evaluator {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    (i : (c : List Bool) → Fin (A c)) (hi : UnaryFn (fun c => (i c).val))
    (p : List Bool → Polynomial ℤ) (E : SpaceFunction (PrimitivePairBits.coefficient p))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value A W (fun c => (p c).toMvPolynomial (i c)) target modulus) := by
  let power (c : List Bool) := FixedWidthQuery.read A W target (pair c (BinaryNatCode.encode (i c).val))
  have hp : power ∈ FP := mem_FP_comp (mem_FP_pair id_mem_FP (bits_mem_FP hi)) (FixedWidthQuery.read_mem_FP hA hW ht)
  have ER := E.precompose (fun c => pair (pair c (power c)) (modulus c)) (mem_FP_pair (mem_FP_pair id_mem_FP hp) hm)
  have hg := supported_FP hA hW i hi ht
  refine (SpaceFunction.branch _ hg.flag_mem_FP ER (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (funext fun c => ?_)
  simp only [decide_eq_true_eq, FixedWidthRowBits.value, DiagonalUnivariateSystem.coefficient]
  rw [← supported_iff]
  by_cases hs : Supported A W i target c
  · rw [ite_eq_left hs, ite_eq_left hs]
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
      pairFst_pair, pairSnd_pair, power]
    rw [FixedWidthQuery.read_packet]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, FixedWidthQuery.entry, (i c).isLt, ite_true]
    rw [RationalSubstitution.IntegerBits.coefficientResidue]
    congr 2
    simp only [FixedWidthPolynomial.nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply, entry_eq_coordinate]
  · rw [ite_eq_right hs, ite_eq_right hs]
    simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.UnivariateRowBits
