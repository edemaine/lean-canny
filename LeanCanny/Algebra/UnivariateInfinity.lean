/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineRingCoordinates
public import LeanCanny.Algebra.HomogenizationAtInfinity
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.EraseLead

/-! # Infinity exclusion for coordinate polynomial grids

At infinity a coordinate equation contributes its leading coefficient times
its highest coordinate power. Nonzero specialized leading coefficients thus
exclude every nonzero common root at infinity, even for repeated equations.
-/

@[expose] public section
open LeanCanny.Algebra MvPolynomial WeightedHomogenization
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.Algebra.UnivariateInfinity
variable {ι R K : Type*} [CommRing R] [Field K]

lemma monomial (i : ι) (k : ℕ) (a : R) :
    (Polynomial.monomial k a).toMvPolynomial i = MvPolynomial.monomial (Finsupp.single i k) a := by
  simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rw [C_mul_X_pow_eq_monomial]

lemma degree_le (p : Polynomial R) (i : ι) : (p.toMvPolynomial i).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def, map_sum]
  apply totalDegree_finsetSum_le
  intro k hk
  rw [monomial]
  exact (totalDegree_monomial_le _ _).trans (by
    simpa using Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk))

variable [Fintype ι]

lemma eval_infinity (p : Polynomial R) (i : ι) (hp : 0 < p.natDegree)
    (phi : R →+* K) (y : Option ι → K) (hy : y none = 0) :
    (homogenize (fun _ => 1) p.natDegree (p.toMvPolynomial i)).eval₂ phi y =
      phi p.leadingCoeff * y (some i) ^ p.natDegree := by
  have hdec : p.toMvPolynomial i = p.eraseLead.toMvPolynomial i + C p.leadingCoeff * X i ^ p.natDegree := by
    have h := congrArg (fun q : Polynomial R => q.toMvPolynomial i) p.eraseLead_add_C_mul_X_pow
    simpa only [map_add, map_mul, map_pow, Polynomial.toMvPolynomial_C,
      Polynomial.toMvPolynomial_X] using h.symm
  have hlow : (p.eraseLead.toMvPolynomial i).totalDegree < p.natDegree :=
    (degree_le p.eraseLead i).trans_lt (p.eraseLead_natDegree_le.trans_lt (Nat.sub_lt hp (by decide)))
  rw [hdec, homogenize_add, eval₂_add, HomogenizationAtInfinity.eval_lower phi _ _ hlow y hy,
    zero_add, homogenize_C_mul, homogenize_X_pow, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]

lemma noInfinity {n : ℕ} (p : Fin n → Polynomial R) (hp : ∀ i, 0 < (p i).natDegree)
    (phi : R →+* ℂ) (hl : ∀ i, phi (p i).leadingCoeff ≠ 0) :
    AffineRingCoordinates.NoInfinity phi (fun i => (p i).toMvPolynomial i)
      (fun i => (p i).natDegree) := by
  intro y hy hz
  funext j
  cases j with
  | none => exact hy
  | some i =>
    have h := hz i
    rw [eval_infinity (p i) i (hp i) phi y hy] at h
    exact (pow_eq_zero_iff (Nat.ne_of_gt (hp i))).mp ((mul_eq_zero.mp h).resolve_left (hl i))
end LeanCanny.Algebra.UnivariateInfinity
