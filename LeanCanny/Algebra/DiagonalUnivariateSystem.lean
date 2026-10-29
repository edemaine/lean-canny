/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialSystemRegularity
public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.Separable

/-! # Diagonal univariate systems preserve degree, mass, and simple roots -/

@[expose] public section
namespace LeanCanny.Algebra.DiagonalUnivariateSystem
open MvPolynomial
open scoped Classical BigOperators
variable {ι : Type*}

private lemma int_algebraMap : algebraMap ℤ (MvPolynomial ι ℤ) = C := Subsingleton.elim _ _

lemma monomial (i : ι) (k : ℕ) (a : ℤ) :
    (Polynomial.monomial k a).toMvPolynomial i = MvPolynomial.monomial (Finsupp.single i k) a := by
  simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, int_algebraMap]
  rw [C_mul_X_pow_eq_monomial]

lemma degree_le (p : Polynomial ℤ) (i : ι) : (p.toMvPolynomial i).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def, map_sum]
  apply totalDegree_finsetSum_le
  intro k hk
  rw [monomial]
  exact (totalDegree_monomial_le _ _).trans (by simpa using Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk))

lemma mass_le (p : Polynomial ℤ) (i : ι) : MvMass.mass (p.toMvPolynomial i) ≤ coefficientMass p := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def, map_sum]
  simp only [monomial]
  apply (MvMass.sum_le _ _).trans
  simp only [MvMass.monomial]
  rw [coefficientMass, Polynomial.sum_def]

lemma coefficient (p : Polynomial ℤ) (i : ι) (e : ι →₀ ℕ) :
    (p.toMvPolynomial i).coeff e = if ∀ j, j ≠ i → e j = 0 then p.coeff (e i) else 0 := by
  classical
  conv_lhs => rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def, map_sum]
  simp only [monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases h : ∀ j, j ≠ i → e j = 0
  · rw [ite_eq_left h]
    have he (k : ℕ) : Finsupp.single i k = e ↔ k = e i := by
      constructor
      · intro hk
        simpa only [Finsupp.single_eq_same] using congrArg (fun u : ι →₀ ℕ => u i) hk
      · intro hk
        ext j
        by_cases hj : j = i
        · subst j; simpa only [Finsupp.single_eq_same] using hk
        · simp [hj, h j hj]
    simp only [he, Finset.sum_ite_eq']
    by_cases hs : e i ∈ p.support
    · simp only [hs, ite_true]
    · simp only [hs, ite_false, Polynomial.notMem_support_iff.mp hs]
  · rw [ite_eq_right h]
    have he (k : ℕ) : Finsupp.single i k ≠ e := by
      intro hk
      apply h
      intro j hj
      rw [← hk]
      simp [hj]
    simp only [he, ite_false, Finset.sum_const_zero]

lemma eval (p : Polynomial ℤ) (i : ι) {K : Type*} [CommRing K] (phi : ℤ →+* K) (x : ι → K) :
    (p.toMvPolynomial i).eval₂ phi x = p.eval₂ phi (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, int_algebraMap, Polynomial.eval₂_monomial, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]

lemma pderiv (p : Polynomial ℤ) (i j : ι) :
    MvPolynomial.pderiv j (p.toMvPolynomial i) = if j = i then p.derivative.toMvPolynomial i else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    split_ifs <;> simp
  | monomial k a =>
    simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, Polynomial.derivative_monomial,
      int_algebraMap, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X]
    by_cases h : j = i
    · subst j
      simp only [Pi.single_eq_same, mul_one, ite_true, map_mul, map_natCast]
      ring
    · simp [h, Ne.symm h]

noncomputable def system (p : ι → Polynomial ℤ) (i : ι) : MvPolynomial ι ℤ := (p i).toMvPolynomial i

variable [Fintype ι]

lemma regular (p : ι → Polynomial ℤ) (hp : ∀ i, ((p i).map (Int.castRingHom ℝ)).Separable)
    (z : ι → ℝ) (hz : ∀ i, (system p i).eval₂ (Int.castRingHom ℝ) z = 0) :
    (fderiv ℝ (fun x => fun i => (system p i).eval₂ (Int.castRingHom ℝ) x) z).IsInvertible := by
  rw [LeanCanny.Geometry.PolynomialSystemRegularity.isInvertible_iff]
  have he : LeanCanny.Geometry.PolynomialSystemRegularity.matrix (Int.castRingHom ℝ) (system p) z =
      Matrix.diagonal (fun i => (p i).derivative.eval₂ (Int.castRingHom ℝ) (z i)) := by
    ext i j
    simp only [LeanCanny.Geometry.PolynomialSystemRegularity.matrix, Matrix.of_apply, system, pderiv, Matrix.diagonal_apply]
    by_cases h : j = i
    · subst j; simp only [ite_true, eval]
    · simp [h, Ne.symm h]
  rw [he, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hroot : ((p i).map (Int.castRingHom ℝ)).eval (z i) = 0 := by
    simpa only [Polynomial.eval_map, system, eval] using hz i
  have h := (hp i).eval₂_derivative_ne_zero (RingHom.id ℝ) (x := z i)
    (by simpa only [Polynomial.eval₂_id] using hroot)
  simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, RingHom.id_comp] using h

end LeanCanny.Algebra.DiagonalUnivariateSystem
