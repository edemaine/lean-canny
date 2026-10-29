/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildParameters
public import LeanCanny.Algebra.FixedWidthRationalSubstitutionSpace

/-! # Uniform coordinate readers for substitution at child parameters -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildReaders
open LeanCanny.Algebra LeanCanny.Computation
open RationalParentChildSource (Inputs count)
open RationalParentChildCoordinates (coordinate parameter coordinateDegree coordinateMass)
open MatrixPower
open scoped Classical
attribute [local irreducible] coordinate

noncomputable def numerator (F : Inputs) (u : List Bool) (i : ℕ) : Polynomial ℤ :=
  (coordinate F (pair u (BinaryNatCode.encode i))).numerator
noncomputable def denominator (F : Inputs) (u : List Bool) (i : ℕ) : Polynomial ℤ :=
  (coordinate F (pair u (BinaryNatCode.encode i))).denominator

def query (q : List Bool) : List Bool :=
  pair (pair (pair (RationalSubstitution.IntegerBits.context q)
    (pairFst (RationalSubstitution.IntegerBits.selectedDegree q)))
      (pairSnd (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem query_FP : query ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
    (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
      (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def readers {F : Inputs} (h : F.Access) :
    RationalSubstitution.IntegerBits.CoordinateReaders (count F) (numerator F) (denominator F) where
  numerator := PrimitivePairBits.coefficient (fun u => (coordinate F u).numerator) ∘ query
  denominator := PrimitivePairBits.coefficient (fun u => (coordinate F u).denominator) ∘ query
  numeratorEvaluator := (RationalParentChildCoordinates.coefficient_evaluators h).1.precompose query query_FP
  denominatorEvaluator := (RationalParentChildCoordinates.coefficient_evaluators h).2.precompose query query_FP
  numerator_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [query, RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [query, RationalSubstitution.IntegerBits.mValue, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  denominator_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [query, RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [query, RationalSubstitution.IntegerBits.mValue, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

theorem coordinate_bounds (F : Inputs) (u : List Bool) (i : ℕ) :
    (numerator F u i).natDegree ≤ coordinateDegree F u ∧
      (denominator F u i).natDegree ≤ coordinateDegree F u ∧
      coefficientMass (numerator F u i) ≤ 2 ^ coordinateMass F u ∧
      coefficientMass (denominator F u i) ≤ 2 ^ coordinateMass F u := by
  have H := RationalParentChildCoordinates.coordinate_bounds F (pair u (BinaryNatCode.encode i))
  simp only [pairFst_pair] at H
  exact ⟨(le_max_left _ _).trans H.1, (le_max_right _ _).trans H.1, H.2.1, H.2.2⟩

theorem denominator_ne_zero (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) (i : Fin (count F u)) :
    (denominator F u i.val).eval₂ (Int.castRingHom ℝ) theta ≠ 0 :=
  (RationalParentChildCoordinates.parameter_root_coordinates F u theta ht i).1

end LeanCanny.Encoding.RationalParentChildReaders
