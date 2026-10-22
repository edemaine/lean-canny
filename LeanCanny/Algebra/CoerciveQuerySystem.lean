/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoerciveApproximation
public import LeanCanny.Algebra.CoerciveCriticalFibers
public import LeanCanny.Algebra.PartialDerivativeDegree
public import LeanCanny.Algebra.MvCoefficientMass

/-! # Integer sign queries for bounded coercive critical samples

Coordinate zero is the positive perturbation parameter. The remaining
coordinates are the original point. The only large coefficient is an
implicit power of two, whose exponent is supplied separately.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveQuerySystem
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def lift (q : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (n + 1)) ℤ :=
  rename Fin.succ q

noncomputable def penalty (D : ℕ) : MvPolynomial (Fin (n + 1)) ℤ :=
  ∑ i : Fin n, X i.succ ^ (2 * D + 2)

noncomputable def objective (q : MvPolynomial (Fin n) ℤ) (D : ℕ) :
    MvPolynomial (Fin (n + 1)) ℤ := lift q ^ 2 + X 0 * penalty D

noncomputable def gradient (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (i : Fin n) :
    MvPolynomial (Fin (n + 1)) ℤ :=
  rename Fin.succ (pderiv i (q ^ 2)) +
    C ((2 * D + 2 : ℕ) : ℤ) * X 0 * X i.succ ^ (2 * D + 1)

noncomputable def residual (q : MvPolynomial (Fin n) ℤ) (E : ℕ) :
    MvPolynomial (Fin (n + 1)) ℤ := lift q ^ 2 - X 0 * C ((2 : ℤ) ^ E)

noncomputable def bound (D E : ℕ) : MvPolynomial (Fin (n + 1)) ℤ :=
  penalty D - C ((2 : ℤ) ^ E)

@[simp] theorem eval_lift (q : MvPolynomial (Fin n) ℤ) (s : ℝ) (x : Fin n → ℝ) :
    eval₂ (Int.castRingHom ℝ) (Fin.cons s x) (lift q) = eval₂ (Int.castRingHom ℝ) x q := by
  simp [lift, eval₂_rename, Function.comp_def]

@[simp] theorem eval_penalty (D : ℕ) (s : ℝ) (x : Fin n → ℝ) :
    eval₂ (Int.castRingHom ℝ) (Fin.cons s x) (penalty D) =
      Geometry.CoercivePolynomialSampling.penalty D x := by
  simp [penalty, Geometry.CoercivePolynomialSampling.penalty]

theorem eval_gradient (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (i : Fin n)
    (s : ℝ) (x : Fin n → ℝ) :
    eval₂ (Int.castRingHom ℝ) (Fin.cons s x) (gradient q D i) =
      eval x (pderiv i (CoerciveCriticalFibers.polynomial (q.map (Int.castRingHom ℝ)) D s)) := by
  have he : eval x (pderiv i ((q.map (Int.castRingHom ℝ)) ^ 2)) =
      eval₂ (Int.castRingHom ℝ) x (pderiv i (q ^ 2)) := by
    rw [← map_pow, pderiv_map, eval_map]
  rw [gradient, CoerciveCriticalFibers.gradient_eq]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, Int.coe_castRingHom, Int.cast_natCast,
    eval₂_X, Fin.cons_zero, Fin.cons_succ, eval₂_rename, Function.comp_def,
    eval_add, eval_monomial, Finsupp.prod_single_index, pow_zero,
    CoerciveCriticalFibers.leadingScalar, he]
  ring

theorem sample_iff (q : MvPolynomial (Fin n) ℤ) (D E : ℕ) (s : ℝ) (x : Fin n → ℝ) :
    Geometry.CoerciveApproximation.Sample (q.map (Int.castRingHom ℝ)) D ((2 : ℝ) ^ E) s x ↔
      (∀ i, eval₂ (Int.castRingHom ℝ) (Fin.cons s x) (gradient q D i) = 0) ∧
      eval₂ (Int.castRingHom ℝ) (Fin.cons s x) (bound (n := n) D E) ≤ 0 ∧
      eval₂ (Int.castRingHom ℝ) (Fin.cons s x) (residual q E) ≤ 0 := by
  simp only [Geometry.CoerciveApproximation.Sample,
    Geometry.CoercivePolynomialSampling.regularization, CoerciveCriticalFibers.polynomial,
    eval_gradient, bound, residual, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C,
    Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat, eval₂_X, Fin.cons_zero,
    eval_lift, eval_penalty, sub_nonpos, eval_map]

theorem lift_mass (q : MvPolynomial (Fin n) ℤ) : MvMass.mass (lift q) ≤ MvMass.mass q :=
  MvMass.rename_le _ _

theorem penalty_mass (D : ℕ) : MvMass.mass (penalty (n := n) D) ≤ n := by
  apply (MvMass.sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by
      simpa only [MvMass.X, one_pow] using MvMass.pow_le (X i.succ : MvPolynomial (Fin (n + 1)) ℤ) (2 * D + 2)
    _ = n := by simp

theorem gradient_mass (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) :
    MvMass.mass (gradient q D i) ≤ 2 * D * MvMass.mass q ^ 2 + (2 * D + 2) := by
  apply (MvMass.add_le _ _).trans
  apply Nat.add_le_add
  · exact (MvMass.rename_le _ _).trans ((MvMass.pderiv_le _ _).trans
      (Nat.mul_le_mul ((MvPolynomial.totalDegree_pow q 2).trans (Nat.mul_le_mul_left 2 hD))
        (MvMass.pow_le q 2)))
  · apply (MvMass.mul_le _ _).trans
    have hpower := MvMass.pow_le (X i.succ : MvPolynomial (Fin (n + 1)) ℤ) (2 * D + 1)
    have hleft := MvMass.mul_le (C ((2 * D + 2 : ℕ) : ℤ) : MvPolynomial (Fin (n + 1)) ℤ) (X 0)
    simp only [MvMass.C, Int.natAbs_natCast, MvMass.X, Nat.mul_one] at hleft
    simpa only [MvMass.X, one_pow, Nat.mul_one] using Nat.mul_le_mul hleft hpower

theorem residual_mass (q : MvPolynomial (Fin n) ℤ) (E : ℕ) :
    MvMass.mass (residual q E) ≤ MvMass.mass q ^ 2 + 2 ^ E := by
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add
  · exact (MvMass.pow_le _ _).trans (Nat.pow_le_pow_left (lift_mass q) 2)
  · simpa only [MvMass.X, MvMass.C, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl, Nat.one_mul] using
      MvMass.mul_le (X 0 : MvPolynomial (Fin (n + 1)) ℤ) (C ((2 : ℤ) ^ E))

theorem bound_mass (D E : ℕ) : MvMass.mass (bound (n := n) D E) ≤ n + 2 ^ E := by
  apply (MvMass.sub_le _ _).trans
  simpa only [MvMass.C, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl] using
    Nat.add_le_add (penalty_mass (n := n) D) (le_refl (2 ^ E))

theorem lift_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) :
    (lift q).totalDegree ≤ D := (totalDegree_rename_le _ _).trans hD

theorem penalty_degree (D : ℕ) : (penalty (n := n) D).totalDegree ≤ 2 * D + 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_X_pow _ _).le

theorem gradient_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) :
    (gradient q D i).totalDegree ≤ 2 * D + 2 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_rename_le _ _).trans ((PartialDerivativeDegree.degree_le _ _).trans
      ((Nat.sub_le _ _).trans ((totalDegree_pow q 2).trans
        ((Nat.mul_le_mul_left 2 hD).trans (by omega)))))
  · have hm := totalDegree_mul (C ((2 * D + 2 : ℕ) : ℤ) * X 0 : MvPolynomial (Fin (n + 1)) ℤ)
      (X i.succ ^ (2 * D + 1))
    have hl := totalDegree_mul (C ((2 * D + 2 : ℕ) : ℤ) : MvPolynomial (Fin (n + 1)) ℤ) (X 0)
    rw [totalDegree_C, totalDegree_X, zero_add] at hl
    rw [totalDegree_X_pow] at hm
    omega

theorem residual_degree (q : MvPolynomial (Fin n) ℤ) (D E : ℕ) (hD : q.totalDegree ≤ D) :
    (residual q E).totalDegree ≤ 2 * D + 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left 2 (lift_degree q D hD)).trans (by omega))
  · have h := totalDegree_mul (X 0 : MvPolynomial (Fin (n + 1)) ℤ) (C ((2 : ℤ) ^ E))
    rw [totalDegree_X, totalDegree_C, add_zero] at h
    omega

theorem bound_degree (D E : ℕ) : (bound (n := n) D E).totalDegree ≤ 2 * D + 2 :=
  (totalDegree_sub _ _).trans (max_le (penalty_degree D) (by rw [totalDegree_C]; omega))

end LeanCanny.Algebra.CoerciveQuerySystem
