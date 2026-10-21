/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicRoots
public import LeanCanny.Algebra.MacaulayProjectiveCriterion

/-! # The projective root criterion for the actual tube polynomial

After specializing its coefficients to an algebraically closed field, the
concrete tube characteristic polynomial vanishes at a parameter exactly
when the shifted tube rows have a nonzero common root. Its constant
coefficient detects common roots of the unshifted tube rows. No condition
on the specialized extraneous determinant is needed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

private theorem criterion_width_bound (source : List Bool → List Bool) (c : List Bool) :
    Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) < 2 ^ TubeCleared.matrixWidth (source c) := by
  have hw := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hw
  exact hw

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
  {K : Type*} [Field K] [IsAlgClosed K]

theorem polynomial_eval_map_eq_zero_iff_exists_common_root (φ : Polynomial (Polynomial ℤ) →+* K) (s : K) :
    Polynomial.eval s ((polynomial source active n d ell c).map φ) = 0 ↔
      ∃ x : Fin (TubeParameter.spatialCount (source c)) → K,
        (∀ i, MvPolynomial.eval₂ φ x (TubeBivariate.rows source active n d ell c i) =
          s * x i ^ (MacaulayBits.Degrees (TubeCleared.layout source) c i)) ∧ ∃ j, x j ≠ 0 := by
  have hW := criterion_width_bound source c
  have hd : ∀ i : Fin (TubeParameter.spatialCount (source c)),
      0 < MacaulayBits.Degrees (TubeCleared.layout source) c i := fun i => TubeCleared.degree_pos source c i.val
  have hdegree := MacaulayUniversal.degree_lt_width _ _ hd hW
  have hp := fun i => (TubeBivariate.rows_homogeneous source active n d ell c i).map φ
  have he := MacaulayUniversal.eval_characteristicQuotient_eq_zero_iff_exists_common_root
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)) hdegree hW
    (fun i => (TubeBivariate.rows source active n d ell c i).map φ) hp hd s
  have hm := Macaulay.characteristicQuotient_map φ (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
  have hi : Polynomial.eval s ((polynomial source active n d ell c).map φ) =
      Polynomial.eval s (Macaulay.characteristicQuotient
        (fun i => (TubeBivariate.rows source active n d ell c i).map φ)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))) :=
    congrArg (Polynomial.eval s) hm
  constructor
  · intro hz
    obtain ⟨x, hx, hnz⟩ := he.mp (hi.symm.trans hz)
    refine ⟨x, fun i => ?_, hnz⟩
    exact (MvPolynomial.eval_map φ x (TubeBivariate.rows source active n d ell c i)).symm.trans (hx i)
  · rintro ⟨x, hx, hnz⟩
    apply hi.trans
    apply he.mpr
    refine ⟨x, fun i => ?_, hnz⟩
    exact (MvPolynomial.eval_map φ x (TubeBivariate.rows source active n d ell c i)).trans (hx i)

theorem polynomial_constant_map_eq_zero_iff_exists_common_root (φ : Polynomial (Polynomial ℤ) →+* K) :
    φ ((polynomial source active n d ell c).coeff 0) = 0 ↔
      ∃ x : Fin (TubeParameter.spatialCount (source c)) → K,
        (∀ i, MvPolynomial.eval₂ φ x (TubeBivariate.rows source active n d ell c i) = 0) ∧ ∃ j, x j ≠ 0 := by
  simpa only [zero_mul, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] using
    polynomial_eval_map_eq_zero_iff_exists_common_root source active n d ell c φ 0

end LeanCanny.ETR.TubeCharacteristicQuotient
