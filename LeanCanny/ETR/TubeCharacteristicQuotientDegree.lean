/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicQuotient
public import LeanCanny.Algebra.CharacteristicQuotientDegree

/-! # Degree of the actual tube quotient over its coefficient fraction field

Faithfully embedding the integer parameter coefficient ring in its fraction
field gives a rational function with the reduced-monomial degree. The count
uses the actual tube degrees and the proved fixed-width coverage condition.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped BigOperators

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

noncomputable def expectedDegree (source : List Bool → List Bool) (c : List Bool) : ℕ :=
  ∑ i : Fin (TubeParameter.spatialCount (source c)),
    ∏ j ∈ Finset.univ.erase i, MacaulayBits.Degrees (TubeCleared.layout source) c j

noncomputable def fractionFieldValue (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    RatFunc (FractionRing (Polynomial (Polynomial ℤ))) :=
  RatFunc.mk
    ((numerator source active n d ell c).map (algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ)))))
    ((TubeExtraneous.characteristicPolynomial source active n d ell c).map
      (algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ)))))

theorem fractionFieldValue_eq_extension (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    fractionFieldValue source active n d ell c =
      PolynomialQuotientDegree.coefficientExtension
        (algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ))))
        (IsFractionRing.injective _ _) (value source active n d ell c) :=
  (PolynomialQuotientDegree.coefficientExtension_mk _ _ _ _).symm

theorem fractionFieldValue_intDegree (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (fractionFieldValue source active n d ell c).intDegree = expectedDegree source c := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.characteristicQuotient_intDegree (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (fun i => TubeCleared.degree_pos source c i.val) (TubeCleared.matrixWidth (source c)) hW
    (algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ))))
    (IsFractionRing.injective _ _)

theorem matrix_size_difference (source : List Bool → List Bool) (c : List Bool) :
    (Macaulay.activeIndices (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).card =
      (TubeExtraneous.indices source c).card + expectedDegree source c := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.card_active_eq_extraneous_add (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (fun i => TubeCleared.degree_pos source c i.val) (TubeCleared.matrixWidth (source c)) hW

theorem expectedDegree_pos (source : List Bool → List Bool) (c : List Bool) : 0 < expectedDegree source c := by
  have hS : 0 < TubeParameter.spatialCount (source c) := by
    unfold TubeParameter.spatialCount
    omega
  let i : Fin (TubeParameter.spatialCount (source c)) := ⟨0, hS⟩
  have hp : 0 < ∏ j ∈ Finset.univ.erase i, MacaulayBits.Degrees (TubeCleared.layout source) c j :=
    Finset.prod_pos (fun j _ => TubeCleared.degree_pos source c j.val)
  apply hp.trans_le
  unfold expectedDegree
  exact Finset.single_le_sum
    (f := fun k : Fin (TubeParameter.spatialCount (source c)) =>
      ∏ j ∈ Finset.univ.erase k, MacaulayBits.Degrees (TubeCleared.layout source) c j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem expectedDegree_le_dimension (source : List Bool → List Bool) (c : List Bool) :
    expectedDegree source c ≤ FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) := by
  have hm := matrix_size_difference source c
  have hc := Finset.card_le_card (Finset.subset_univ
    (Macaulay.activeIndices (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change _ ≤ FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) at hc
  omega

theorem fractionFieldValue_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    fractionFieldValue source active n d ell c ≠ 0 := by
  intro hz
  have h := fractionFieldValue_intDegree source active n d ell c
  rw [hz, RatFunc.intDegree_zero] at h
  have hp := expectedDegree_pos source c
  omega

theorem polynomial_quotient_natDegree (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
    (q : Polynomial (Polynomial (Polynomial ℤ)))
    (hq : numerator source active n d ell c = q * TubeExtraneous.characteristicPolynomial source active n d ell c) :
    q.natDegree = expectedDegree source c := by
  let φ := algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ)))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hn : (TubeExtraneous.characteristicPolynomial source active n d ell c).map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff hφ).mpr (denominator_ne_zero source active n d ell c)
  have hv : fractionFieldValue source active n d ell c =
      algebraMap (Polynomial (FractionRing (Polynomial (Polynomial ℤ)))) (RatFunc (FractionRing (Polynomial (Polynomial ℤ)))) (q.map φ) := by
    rw [fractionFieldValue, hq, Polynomial.map_mul, RatFunc.mk_eq_div, map_mul]
    exact mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero hn)
  have hd := fractionFieldValue_intDegree source active n d ell c
  rw [hv, RatFunc.intDegree_polynomial, Polynomial.natDegree_map_eq_of_injective hφ] at hd
  exact_mod_cast hd

end LeanCanny.ETR.TubeCharacteristicQuotient
