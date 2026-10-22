/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicQuotientDegree
public import LeanCanny.Algebra.MacaulayCharacteristicQuotient

/-! # A concrete polynomial for the actual tube characteristic quotient

The polynomial is defined by monic division over the original integer
parameter ring. It represents the existing rational quotient, has the
proved reduced-monomial degree and dimension-sign leading coefficient,
and realizes the prior order and lowest-coefficient data. Its degree
survives every specialization to a nontrivial coefficient ring.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

private theorem polynomial_width_bound (source : List Bool → List Bool) (c : List Bool) :
    Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) < 2 ^ TubeCleared.matrixWidth (source c) := by
  have hw := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hw
  exact hw

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def polynomial : Polynomial (Polynomial (Polynomial ℤ)) :=
  Macaulay.characteristicQuotient (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

theorem polynomial_factorization : numerator source active n d ell c =
    polynomial source active n d ell c * TubeExtraneous.characteristicPolynomial source active n d ell c := by
  have he := Macaulay.characteristicQuotient_factorization (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c)
    (fun i => TubeCleared.degree_pos source c i.val) (polynomial_width_bound source c)
  change numerator source active n d ell c = TubeExtraneous.characteristicPolynomial source active n d ell c *
    polynomial source active n d ell c at he
  exact he.trans (mul_comm (TubeExtraneous.characteristicPolynomial source active n d ell c)
    (polynomial source active n d ell c))

theorem polynomial_ne_zero : polynomial source active n d ell c ≠ 0 := by
  intro hz
  have he := polynomial_factorization source active n d ell c
  rw [hz, zero_mul] at he
  exact numerator_ne_zero source active n d ell c he

theorem value_eq_polynomial : value source active n d ell c =
    RatFunc.coePolynomial (polynomial source active n d ell c) :=
  Macaulay.characteristicQuotient_ratFunc (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c)
    (fun i => TubeCleared.degree_pos source c i.val) (polynomial_width_bound source c)

theorem polynomial_natDegree : (polynomial source active n d ell c).natDegree = expectedDegree source c :=
  polynomial_quotient_natDegree source active n d ell c _ (polynomial_factorization source active n d ell c)

theorem polynomial_leadingCoeff : (polynomial source active n d ell c).leadingCoeff =
    (-1 : Polynomial (Polynomial ℤ)) ^ expectedDegree source c :=
  Macaulay.characteristicQuotient_leadingCoeff (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (fun i => TubeCleared.degree_pos source c i.val) (polynomial_width_bound source c)

theorem polynomial_signed_monic :
    (Polynomial.C ((-1 : Polynomial (Polynomial ℤ)) ^ expectedDegree source c) * polynomial source active n d ell c).Monic :=
  Macaulay.characteristicQuotient_signed_monic (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (fun i => TubeCleared.degree_pos source c i.val) (polynomial_width_bound source c)

theorem polynomial_natDegree_map {S : Type*} [CommRing S] [Nontrivial S]
    (φ : Polynomial (Polynomial ℤ) →+* S) :
    ((polynomial source active n d ell c).map φ).natDegree = expectedDegree source c :=
  Macaulay.characteristicQuotient_natDegree_map φ (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (fun i => TubeCleared.degree_pos source c i.val) (polynomial_width_bound source c)

theorem polynomial_map_ne_zero {S : Type*} [CommRing S] [Nontrivial S]
    (φ : Polynomial (Polynomial ℤ) →+* S) : (polynomial source active n d ell c).map φ ≠ 0 := by
  intro hz
  have he := polynomial_natDegree_map source active n d ell c φ
  rw [hz, Polynomial.natDegree_zero] at he
  exact (Nat.ne_of_gt (expectedDegree_pos source c)) he.symm

theorem polynomial_map_roots_card_le {K : Type*} [Field K]
    (φ : Polynomial (Polynomial ℤ) →+* K) :
    ((polynomial source active n d ell c).map φ).roots.card ≤ expectedDegree source c := by
  rw [← polynomial_natDegree_map source active n d ell c φ]
  exact Polynomial.card_roots' _

theorem order_eq_polynomial : order source active n d ell c = (polynomial source active n d ell c).natTrailingDegree :=
  (of_polynomial source active n d ell c _ (polynomial_factorization source active n d ell c)).1

theorem lowestCoefficient_eq_polynomial : lowestCoefficient source active n d ell c =
    algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ)))
      (polynomial source active n d ell c).trailingCoeff :=
  (of_polynomial source active n d ell c _ (polynomial_factorization source active n d ell c)).2

theorem order_nonneg : 0 ≤ order source active n d ell c := by
  rw [order_eq_polynomial]
  exact Int.natCast_nonneg _

theorem polynomial_natTrailingDegree_le : (polynomial source active n d ell c).natTrailingDegree ≤ expectedDegree source c := by
  rw [← polynomial_natDegree source active n d ell c]
  exact Polynomial.natTrailingDegree_le_natDegree _

theorem negativeOrder_eq_empty : {c | order source active n d ell c < 0} = ∅ := by
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact not_lt_of_ge (order_nonneg source active n d ell c)

end LeanCanny.ETR.TubeCharacteristicQuotient
