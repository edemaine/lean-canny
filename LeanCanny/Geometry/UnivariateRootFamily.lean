/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialRootFamily
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.Separable

/-! # Spatial regularity of univariate polynomial families

A separable fiber gives the actual invertible spatial derivative of its
one-variable root system. Coefficients may themselves be parameter polynomials.
-/

@[expose] public section
namespace LeanCanny.Geometry.UnivariateRootFamily
open LeanCanny.Algebra MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {R S ι : Type*} [CommRing R] [CommRing S]

lemma eval (p : Polynomial R) (i : ι) (phi : R →+* S) (x : ι → S) :
    (p.toMvPolynomial i).eval₂ phi x = p.eval₂ phi (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq,
      Polynomial.eval₂_monomial, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]

lemma pderiv (p : Polynomial R) (i j : ι) :
    MvPolynomial.pderiv j (p.toMvPolynomial i) = if j = i then p.derivative.toMvPolynomial i else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    split_ifs <;> simp
  | monomial k a =>
    simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, Polynomial.derivative_monomial,
      MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X]
    by_cases h : j = i
    · subst j
      simp only [Pi.single_eq_same, mul_one, ite_true, map_mul, map_natCast]
      ring
    · simp [h, Ne.symm h]

noncomputable def rows (Q : Polynomial (Polynomial ℝ)) : Fin 1 → MvPolynomial (Fin 1) (Polynomial ℝ) :=
  fun _ => Q.toMvPolynomial 0

lemma regular (Q : Polynomial (Polynomial ℝ)) (t : ℝ) (x : Fin 1 → ℝ)
    (hsep : (Q.map (Polynomial.evalRingHom t)).Separable)
    (hx : PolynomialRootFamily.value (rows Q) (t, x) = 0) :
    (fderiv ℝ (PolynomialRootFamily.value (rows Q)) (t, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin 1 → ℝ)).IsInvertible := by
  rw [PolynomialRootFamily.isInvertible_iff, PolynomialRootFamily.eval_jacobian, Matrix.det_fin_one]
  change (MvPolynomial.pderiv 0 (Q.toMvPolynomial (0 : Fin 1))).eval₂ (Polynomial.evalRingHom t) x ≠ 0
  rw [pderiv, ite_eq_left rfl, eval]
  have H := congrFun hx 0
  change (Q.toMvPolynomial (0 : Fin 1)).eval₂ (Polynomial.evalRingHom t) x = 0 at H
  rw [eval] at H
  have hd := hsep.eval₂_derivative_ne_zero (RingHom.id ℝ) (x := x 0) (by
    simpa only [Polynomial.eval₂_id, Polynomial.eval_map, Pi.zero_apply] using H)
  simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, RingHom.id_comp] using hd

/-- Independent coordinate equations form a square polynomial system. -/
noncomputable def diagonal (Q : ι → Polynomial (Polynomial ℝ)) :
    ι → MvPolynomial ι (Polynomial ℝ) := fun i => (Q i).toMvPolynomial i

lemma value_diagonal (Q : ι → Polynomial (Polynomial ℝ)) (t : ℝ) (x : ι → ℝ) (i : ι) :
    PolynomialRootFamily.value (diagonal Q) (t, x) i =
      (Q i).eval₂ (Polynomial.evalRingHom t) (x i) :=
  eval (Q i) i (Polynomial.evalRingHom t) x

variable [Fintype ι] [DecidableEq ι]

/-- All coordinate roots are regular when every specialized equation is
separable. This includes the empty coordinate family. -/
lemma regular_diagonal (Q : ι → Polynomial (Polynomial ℝ)) (t : ℝ) (x : ι → ℝ)
    (hsep : ∀ i, ((Q i).map (Polynomial.evalRingHom t)).Separable)
    (hx : PolynomialRootFamily.value (diagonal Q) (t, x) = 0) :
    (fderiv ℝ (PolynomialRootFamily.value (diagonal Q)) (t, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible := by
  rw [PolynomialRootFamily.isInvertible_iff, PolynomialRootFamily.eval_jacobian]
  have hmatrix : (fun i j => (MvPolynomial.pderiv j (diagonal Q i)).eval₂
      (Polynomial.evalRingHom t) x) =
      Matrix.diagonal (fun i => (Q i).derivative.eval₂ (Polynomial.evalRingHom t) (x i)) := by
    ext i j
    dsimp only [diagonal]
    rw [pderiv]
    by_cases h : j = i
    · subst j
      simp only [ite_true, eval, Matrix.diagonal_apply_eq]
    · simp [h, Ne.symm h, Matrix.diagonal_apply_ne]
  rw [hmatrix, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have H := congrFun hx i
  rw [value_diagonal] at H
  have hd := (hsep i).eval₂_derivative_ne_zero (RingHom.id ℝ) (x := x i) (by
    simpa only [Polynomial.eval₂_id, Polynomial.eval_map, Pi.zero_apply] using H)
  simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, RingHom.id_comp] using hd
end LeanCanny.Geometry.UnivariateRootFamily
