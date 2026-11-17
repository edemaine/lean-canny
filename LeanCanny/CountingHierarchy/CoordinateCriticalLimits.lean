/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCoordinatePolynomial
public import LeanCanny.CountingHierarchy.PolynomialFilteredLimit
public import LeanCanny.CountingHierarchy.IntegerBivariate
public import LeanCanny.Geometry.UnboundedCoerciveComponents

/-! # Coordinate candidates meeting every selected closed zero-set part

The existing constrained coercive sampling theorem supplies bounded critical
limits in any nonempty relatively clopen part of a zero set. Zero-center
pure-power characteristic polynomials provide coordinate equations for that
same limit. No equations describing the selected part are needed.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial Filter Set LeanCanny.Algebra
open scoped Topology Classical

variable {n : ℕ}

theorem criticalLower_of_coercive_gradient (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (s : ℝ) (hs : 0 < s) (x : Fin n → ℝ)
    (hx : ∀ i, eval x (pderiv i (Geometry.CoercivePolynomialSampling.regularization q D s)) = 0) :
    ∀ i, MvPolynomial.aeval x (criticalLower (2 * D + 1) (fun _ => 0)
      (s * (2 * D + 2 : ℕ))⁻¹ (q ^ 2) i) = x i ^ (2 * D + 1) := by
  intro i
  have h := hx i
  change eval x (pderiv i (CoerciveCriticalFibers.polynomial q D s)) = 0 at h
  rw [CoerciveCriticalFibers.gradient_eq] at h
  simp only [map_add, MvPolynomial.eval_monomial, Finsupp.prod_single_index, pow_zero,
    CoerciveCriticalFibers.leadingScalar] at h
  have hc : (s * ((2 * D + 2 : ℕ) : ℝ)) ≠ 0 := mul_ne_zero hs.ne' (by positivity)
  simp only [criticalLower, zero_pow (by omega : 2 * D + 1 ≠ 0), map_zero,
    map_sub, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_eq_eval]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, zero_sub]
  field_simp [hc]
  nlinarith

noncomputable def candidateCoordinate (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : Polynomial ℤ :=
  let d := 2 * (D + 1)
  (Bivariate.swap (parametricCoordinatePolynomial d (q ^ 2)
    (totalDegree_pow q 2 |>.trans (by dsimp only [d]; nlinarith)) i)).leadingCoeff

theorem candidateCoordinate_ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : candidateCoordinate q D hD i ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro he
  have hz := congrArg Bivariate.swap he
  simp only [Bivariate.swap_swap_apply, map_zero] at hz
  exact (parametricCoordinatePolynomial_monic _ _ _ i).ne_zero hz

end LeanCanny.CountingHierarchy
