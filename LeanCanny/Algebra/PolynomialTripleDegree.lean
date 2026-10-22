/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialKronecker

/-! # Inner degree of determinants with three independent parameters

Rotating the innermost variable to the outermost position turns a uniform
coefficient-degree allowance into an ordinary polynomial degree bound. The
rotation is a ring map, so columnwise bounds pass through determinants.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialTripleDegree
open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def rotate : Polynomial (Polynomial (Polynomial R)) →+* Polynomial (Polynomial (Polynomial R)) :=
  (Polynomial.Bivariate.swap (R := Polynomial R)).toRingHom.comp
    (Polynomial.mapRingHom (Polynomial.Bivariate.swap (R := R)).toRingHom)

theorem rotate_coefficient (p : Polynomial (Polynomial (Polynomial R))) (i j k : ℕ) :
    (((rotate p).coeff i).coeff j).coeff k = ((p.coeff j).coeff k).coeff i := by
  have h := congrArg (fun q : Polynomial R => q.coeff k)
    (PolynomialKronecker.swap_coefficient (p.map (Polynomial.Bivariate.swap (R := R)).toRingHom) i j)
  rw [Polynomial.coeff_map] at h
  change (((rotate p).coeff i).coeff j).coeff k = ((Polynomial.Bivariate.swap (p.coeff j)).coeff i).coeff k at h
  exact h.trans (PolynomialKronecker.swap_coefficient (p.coeff j) i k)

theorem degree_iff_rotate (p : Polynomial (Polynomial (Polynomial R))) (D : ℕ) :
    (∀ j k, ((p.coeff j).coeff k).natDegree ≤ D) ↔ (rotate p).natDegree ≤ D := by
  constructor
  · intro hp
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext j k
    rw [rotate_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt ((hp j k).trans_lt hi)]
    simp
  · intro hp j k
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [← rotate_coefficient p i j k, Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt hi)]
    simp

theorem determinant_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Polynomial (Polynomial R)))) (D : ι → ℕ)
    (hD : ∀ r s j k, (((A r s).coeff j).coeff k).natDegree ≤ D s) (j k : ℕ) :
    (((A.det.coeff j).coeff k).natDegree) ≤ ∑ s, D s := by
  have hd : (rotate A.det).natDegree ≤ ∑ s, D s := by
    let φ : Polynomial (Polynomial (Polynomial R)) →+* Polynomial (Polynomial (Polynomial R)) := rotate
    have hm := RingHom.map_det (R := Polynomial (Polynomial (Polynomial R))) (S := Polynomial (Polynomial (Polynomial R))) φ A
    change rotate A.det = (A.map φ).det at hm
    rw [hm]
    apply det_natDegree_le _ D
    intro r s
    exact (degree_iff_rotate (A r s) (D s)).mp (hD r s)
  exact (degree_iff_rotate A.det _).mpr hd j k

end LeanCanny.Algebra.PolynomialTripleDegree
