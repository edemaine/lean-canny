/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicPolynomial
public import LeanCanny.Algebra.MacaulayProjectiveRoots

/-! # Common roots of the actual tube system annihilate its polynomial quotient

After any coefficient specialization to a domain, every nonzero common
root of the characteristic-shifted tube rows is a root of the concrete
characteristic quotient polynomial. At parameter zero this annihilates
the constant coefficient for every common root of the original tube rows.
No nonvanishing hypothesis on the extraneous determinant is needed.
The converse over algebraically closed fields is proved in
`TubeCharacteristicCriterion`.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

private theorem root_width_bound (source : List Bool → List Bool) (c : List Bool) :
    Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) < 2 ^ TubeCleared.matrixWidth (source c) := by
  have hw := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hw
  exact hw

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
  {K : Type*} [CommRing K] [IsDomain K]

theorem polynomial_eval_map_eq_zero_of_common_root (φ : Polynomial (Polynomial ℤ) →+* K)
    (s : K) (x : Fin (TubeParameter.spatialCount (source c)) → K)
    (hx : ∀ i, MvPolynomial.eval₂ φ x (TubeBivariate.rows source active n d ell c i) =
      s * x i ^ (MacaulayBits.Degrees (TubeCleared.layout source) c i)) (hnz : ∃ j, x j ≠ 0) :
    Polynomial.eval s ((polynomial source active n d ell c).map φ) = 0 := by
  exact MacaulayUniversal.eval_map_characteristicQuotient_eq_zero_of_common_root φ
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (MacaulayUniversal.degree_lt_width _ _ (fun i => TubeCleared.degree_pos source c i.val) (root_width_bound source c))
    (root_width_bound source c) (TubeBivariate.rows source active n d ell c)
    (TubeBivariate.rows_homogeneous source active n d ell c)
    (fun i => TubeCleared.degree_pos source c i.val) s x hx hnz

theorem polynomial_constant_map_eq_zero_of_common_root (φ : Polynomial (Polynomial ℤ) →+* K)
    (x : Fin (TubeParameter.spatialCount (source c)) → K)
    (hx : ∀ i, MvPolynomial.eval₂ φ x (TubeBivariate.rows source active n d ell c i) = 0) (hnz : ∃ j, x j ≠ 0) :
    φ ((polynomial source active n d ell c).coeff 0) = 0 := by
  have he := polynomial_eval_map_eq_zero_of_common_root source active n d ell c φ 0 x
    (fun i => by simpa only [zero_mul] using hx i) hnz
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] using he

end LeanCanny.ETR.TubeCharacteristicQuotient
