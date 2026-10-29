/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Algebra.PolynomialProductSpace
public import LeanCanny.Algebra.ModularSumSpace

/-! # Native modular coefficients of an indexed sum of polynomial squares -/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialSumSquaresBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Polynomial
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

def factorQuery (q : List Bool) :=
  pair (pair (context (pairFst q)) (pairSnd (pairSnd q))) (pairSnd (pairFst q))

theorem factorQuery_FP : factorQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp (f := pairFst) (g := context) pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem square_evaluator (p : List Bool → Polynomial ℤ)
    (E : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => p c ^ 2)) := by
  let P : PolynomialProduct.ModularFamily := {
    count _ := 2
    modulus := mValue
    degree q := Nat.fromBitsLE (selectedDegree q)
    factor q _ := (p (context q)).map (Int.castRingHom (ZMod (mValue q)))
    modulus_ne_zero q := by dsimp [mValue]; omega }
  let A : PolynomialProduct.ModularAccess P := {
    count _ := BinaryNatCode.encode 2
    modulus q := BinaryNat.succ (pairSnd q)
    degree q := BinaryNat.normalize (selectedDegree q)
    coefficient := PrimitivePairBits.coefficient p ∘ factorQuery
    count_eq _ := rfl
    modulus_eq _ := BinaryNat.succ_eq_bits _
    degree_eq _ := BinaryNat.normalize_eq_bits _
    coefficient_eq c i _ k := by
      simp only [Function.comp_apply, factorQuery, PrimitivePairBits.coefficient, context, selectedDegree,
        mValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, P, coeff_map]
      rfl }
  have hA : A.ControlsPolyTime := ⟨constFn_mem_FP _, mem_FP_comp (f := pairSnd) (g := BinaryNat.succ) pairSnd_mem_FP BinaryNat.succ_mem_FP,
    mem_FP_comp (f := selectedDegree) (g := BinaryNat.normalize) RationalSubstitution.IntegerBits.selectedDegree_mem_FP BinaryNat.normalize_mem_FP⟩
  have H := A.evaluator hA (E.precompose factorQuery factorQuery_FP)
  refine H.congr (funext fun q => ?_)
  simp only [PolynomialProduct.ModularFamily.value, P, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, PrimitivePairBits.coefficient, ← Polynomial.map_mul, coeff_map, coefficientResidue, pow_two, Int.coe_castRingHom]

noncomputable def polynomial (p : List Bool → Polynomial ℤ) (n : List Bool → ℕ) (c : List Bool) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (n c), p (pair c (BinaryNatCode.encode i)) ^ 2

def sumQuery (q : List Bool) := pair
  (pair (pair (context (pairFst q)) (pairSnd q)) (selectedDegree (pairFst q))) (pairSnd (pairFst q))

theorem sumQuery_FP : sumQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := context) pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp (f := pairFst) (g := selectedDegree) pairFst_mem_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP))
  (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem evaluator (p : List Bool → Polynomial ℤ) (n : List Bool → ℕ) (hn : BinaryFn n)
    (E : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p n)) := by
  have H := (square_evaluator p E).precompose sumQuery sumQuery_FP
  have hN : BinaryFn (fun q => n (context q)) := hn.comp RationalSubstitution.IntegerBits.context_mem_FP
  have hc := hN.bits_mem_FP
  have hm := mem_FP_comp (f := pairSnd) (g := BinaryNat.succ) pairSnd_mem_FP BinaryNat.succ_mem_FP
  have R := ModularSum.evaluatorWithModulus H _ _ hc hm mValue
    (funext fun q => by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, mValue])
    (fun c i => ((p (pair (context c) (BinaryNatCode.encode i)) ^ 2).coeff (Nat.fromBitsLE (selectedDegree c)) : ZMod (mValue c)))
    (fun c => by dsimp [mValue]; omega) (fun c i _ => by
      simp only [Function.comp_apply, sumQuery, PrimitivePairBits.coefficient, context, selectedDegree, mValue,
        pairFst_pair, pairSnd_pair]
      rfl)
  refine R.congr (funext fun q => ?_)
  simp only [PrimitivePairBits.coefficient, polynomial, coefficientResidue, finsetSum_coeff, Int.cast_sum,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.PolynomialSumSquaresBits
