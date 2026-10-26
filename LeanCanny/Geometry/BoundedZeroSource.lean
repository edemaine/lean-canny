/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoercivePolynomialSampling
public import LeanCanny.Geometry.ProjectionCritical
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Size

/-! # A compact polynomial source for bounded zero sets

Two new real coordinates impose a sphere equation. Squaring this equation
and the original polynomial gives a nonnegative energy with compact sublevels.
Its zeros have an explicit coordinate radius. Degree and mass allowances are
derived from the original polynomial and binary radius exponent.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedZeroSource
open MvPolynomial Set LeanCanny.Algebra
open scoped BigOperators

variable {n : ℕ}

def radiusSquared (R : ℕ) : ℤ := 2 ^ (2 * R)

noncomputable def radial {k : ℕ} (x : Fin k → ℝ) : ℝ := ∑ i, x i ^ 2

noncomputable def sphere (n R : ℕ) : MvPolynomial (Fin (n + 2)) ℤ :=
  (∑ i : Fin (n + 2), X i ^ 2) - C (radiusSquared R)

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (R : ℕ) : MvPolynomial (Fin (n + 2)) ℤ :=
  (rename (Fin.castAdd 2) q) ^ 2 + sphere n R ^ 2

def degreeAllowance (D : ℕ) : ℕ := 2 * (D + 2)
def barrierMassExponent (n R : ℕ) : ℕ := 2 * R + (n + 3).size
def massExponent (n b R : ℕ) : ℕ := 2 * b + 2 * barrierMassExponent n R + 1
def powerHalfDegree (D : ℕ) : ℕ := 2 * degreeAllowance D + 1
def powerDegree (D : ℕ) : ℕ := 2 * powerHalfDegree D

theorem powerHalfDegree_odd (D : ℕ) : Odd (powerHalfDegree D) := ⟨degreeAllowance D, rfl⟩

theorem powerDegree_even (D : ℕ) : Even (powerDegree D) := by
  exact ⟨powerHalfDegree D, by unfold powerDegree; omega⟩

theorem degreeAllowance_lt_power (D : ℕ) : degreeAllowance D < powerDegree D := by
  unfold powerDegree powerHalfDegree
  omega

theorem eval_polynomial (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (w : Fin (n + 2) → ℝ) :
    (polynomial q R).eval₂ (Int.castRingHom ℝ) w =
      (q.eval₂ (Int.castRingHom ℝ) (fun i => w (i.castAdd 2))) ^ 2 +
        (radial w - (radiusSquared R : ℝ)) ^ 2 := by
  simp only [polynomial, sphere, eval₂_add, eval₂_pow, eval₂_rename, Function.comp_def,
    eval₂_sub, eval₂_sum, eval₂_X, eval₂_C, Int.coe_castRingHom, radial]

theorem nonneg (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (w : Fin (n + 2) → ℝ) :
    0 ≤ (polynomial q R).eval₂ (Int.castRingHom ℝ) w := by
  rw [eval_polynomial]
  positivity

theorem zero_iff (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (w : Fin (n + 2) → ℝ) :
    (polynomial q R).eval₂ (Int.castRingHom ℝ) w = 0 ↔
      q.eval₂ (Int.castRingHom ℝ) (fun i => w (i.castAdd 2)) = 0 ∧ radial w = (radiusSquared R : ℝ) := by
  rw [eval_polynomial, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),
    sq_eq_zero_iff, sq_eq_zero_iff, sub_eq_zero]

theorem compact_sublevels (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (e : ℝ) :
    IsCompact {w : Fin (n + 2) → ℝ | (polynomial q R).eval₂ (Int.castRingHom ℝ) w ≤ e} := by
  have hc : IsClosed {w : Fin (n + 2) → ℝ | (polynomial q R).eval₂ (Int.castRingHom ℝ) w ≤ e} :=
    isClosed_le (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (polynomial q R)).continuous continuous_const
  apply (CoercivePolynomialSampling.isCompact_sublevel (n := n + 2) 0
    (e + (radiusSquared R : ℝ) ^ 2 + 2)).of_isClosed_subset hc
  intro w hw
  change (polynomial q R).eval₂ (Int.castRingHom ℝ) w ≤ e at hw
  rw [eval_polynomial] at hw
  change radial w ≤ e + (radiusSquared R : ℝ) ^ 2 + 2
  have hr : 0 ≤ radial w := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg (radial w - (radiusSquared R : ℝ) - 1),
    sq_nonneg ((radiusSquared R : ℝ) - 1),
    sq_nonneg (q.eval₂ (Int.castRingHom ℝ) (fun i => w (i.castAdd 2)))]

theorem zero_coordinate_bound (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (w : Fin (n + 2) → ℝ)
    (hw : (polynomial q R).eval₂ (Int.castRingHom ℝ) w = 0) (i : Fin (n + 2)) : |w i| ≤ 2 ^ R := by
  have hsum := (zero_iff q R w).mp hw |>.2
  have hi : w i ^ 2 ≤ radial w := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hsum] at hi
  have he : (radiusSquared R : ℝ) = (2 ^ R : ℝ) ^ 2 := by
    simp only [radiusSquared, Int.cast_pow, Int.cast_ofNat, ← pow_mul, Nat.mul_comm 2 R]
  rw [he] at hi
  exact abs_le_of_sq_le_sq hi (by positivity)

theorem sphere_degree (n R : ℕ) : (sphere n R).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ _).trans (by simp)
  · exact (totalDegree_C _).le.trans (by decide)

theorem degree_bound (q : MvPolynomial (Fin n) ℤ) (D R : ℕ) (hD : q.totalDegree ≤ D) :
    (polynomial q R).totalDegree ≤ degreeAllowance D := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left 2 ((totalDegree_rename_le _ _).trans hD)).trans
      (by unfold degreeAllowance; omega))
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left 2 (sphere_degree n R)).trans
      (by unfold degreeAllowance; omega))

theorem sphere_mass (n R : ℕ) : MvMass.mass (sphere n R) ≤ 2 ^ barrierMassExponent n R := by
  have hs : MvMass.mass (∑ i : Fin (n + 2), (X i : MvPolynomial (Fin (n + 2)) ℤ) ^ 2) ≤ n + 2 := by
    apply (MvMass.sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin (n + 2), (1 : ℕ) := Finset.sum_le_sum (fun i _ => by simpa using MvMass.pow_le (X i) 2)
      _ = n + 2 := by simp
  have hc : MvMass.mass (C (radiusSquared R) : MvPolynomial (Fin (n + 2)) ℤ) = 2 ^ (2 * R) := by
    simp only [MvMass.C, radiusSquared, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
  apply (MvMass.sub_le _ _).trans
  calc
    _ ≤ (n + 2) + 2 ^ (2 * R) := Nat.add_le_add hs hc.le
    _ ≤ (n + 3) * 2 ^ (2 * R) := by nlinarith [Nat.mul_le_mul_left (n + 2) (Nat.one_le_two_pow (n := 2 * R))]
    _ ≤ 2 ^ (n + 3).size * 2 ^ (2 * R) := Nat.mul_le_mul_right _ (Nat.lt_size_self (n + 3)).le
    _ = _ := by rw [← pow_add, Nat.add_comm]; rfl

theorem mass_bound (q : MvPolynomial (Fin n) ℤ) (b R : ℕ) (hq : MvMass.mass q ≤ 2 ^ b) :
    MvMass.mass (polynomial q R) ≤ 2 ^ massExponent n b R := by
  have hq' := ((MvMass.pow_le (rename (Fin.castAdd 2) q) 2).trans
    (Nat.pow_le_pow_left ((MvMass.rename_le _ _).trans hq) 2))
  have hs := (MvMass.pow_le (sphere n R) 2).trans (Nat.pow_le_pow_left (sphere_mass n R) 2)
  rw [← pow_mul, Nat.mul_comm b 2] at hq'
  rw [← pow_mul, Nat.mul_comm (barrierMassExponent n R) 2] at hs
  apply (MvMass.add_le _ _).trans
  apply (Nat.add_le_add hq' hs).trans
  have h1 : 2 ^ (2 * b) ≤ 2 ^ (2 * b + 2 * barrierMassExponent n R) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ (2 * barrierMassExponent n R) ≤ 2 ^ (2 * b + 2 * barrierMassExponent n R) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold massExponent
  rw [pow_succ]
  omega

end LeanCanny.Geometry.BoundedZeroSource
