/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-! # The separated even-power potential in the coercive deformation -/

public section

namespace LeanCanny.CountingHierarchy

open Set
open scoped BigOperators

@[expose] def powerPotential (ell : ℕ) (a t : ℝ) : ℝ :=
  t ^ (ell + 1) - (ell + 1 : ℕ) * a ^ ell * t + (ell + 1 : ℕ) * a ^ (ell + 1)

/-- The tangent inequality is valid for negative arguments as well as
 positive ones, since the leading exponent is even. -/
theorem powerPotential_lower (ell : ℕ) (he : Even (ell + 1)) (a t : ℝ) (ha : 0 ≤ a) :
    a ^ (ell + 1) ≤ powerPotential ell a t := by
  by_cases ht : -a ≤ t
  · have h := pow_add_mul_le_add_pow ha (show 0 ≤ 2 * a + (t - a) from by linarith) (ell + 1)
    simp only [Nat.add_sub_cancel, add_sub_cancel] at h
    unfold powerPotential
    simp only [Nat.cast_add, Nat.cast_one, pow_succ] at h ⊢
    nlinarith
  · have ht0 : t ≤ 0 := by linarith
    have hp := he.pow_nonneg t
    have hap := pow_nonneg ha ell
    have hap' := pow_nonneg ha (ell + 1)
    have hm : (1 : ℝ) ≤ (ell + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le ell)
    have hlin : (ell + 1 : ℕ) * a ^ ell * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) ht0
    unfold powerPotential
    nlinarith

/-- A convenient explicit coordinate bound for each potential sublevel. -/
theorem abs_le_powerPotential (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a t : ℝ) (ha : 0 ≤ a) :
    |t| ≤ powerPotential ell a t + (ell + 1 : ℕ) * a ^ ell + 1 := by
  have hg : 0 ≤ powerPotential ell a t := (pow_nonneg ha _).trans (powerPotential_lower ell he a t ha)
  have hcoef : 0 ≤ (ell + 1 : ℕ) * a ^ ell := by positivity
  have hc : 0 ≤ (ell + 1 : ℕ) * a ^ (ell + 1) := by positivity
  by_cases ht : |t| ≤ (ell + 1 : ℕ) * a ^ ell + 1
  · linarith
  · have ht1 : 1 ≤ |t| := by linarith
    by_cases ht0 : t < 0
    · have hp : |t| ≤ t ^ (ell + 1) := by
        have hh := le_self_pow₀ ht1 (show ell + 1 ≠ 0 by omega)
        rwa [← abs_pow, abs_of_nonneg (he.pow_nonneg t)] at hh
      have hlin : (ell + 1 : ℕ) * a ^ ell * t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef ht0.le
      unfold powerPotential
      linarith
    · have htpos : 0 ≤ t := le_of_not_gt ht0
      rw [abs_of_nonneg htpos] at ht ⊢
      have htge : 1 ≤ t := by linarith
      have hp : t ≤ t ^ ell := le_self_pow₀ htge (by omega)
      have hsquare : t * t ≤ t ^ (ell + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right hp htpos
      unfold powerPotential
      nlinarith

@[expose] def separatedPotential {n : ℕ} (ell : ℕ) (a x : Fin n → ℝ) : ℝ :=
  ∑ i, powerPotential ell (a i) (x i)

theorem separatedPotential_nonneg {n : ℕ} (ell : ℕ) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (x : Fin n → ℝ) :
    0 ≤ separatedPotential ell a x := by
  exact Finset.sum_nonneg (fun i _ => (pow_nonneg (ha i) _).trans
    (powerPotential_lower ell he (a i) (x i) (ha i)))

theorem continuous_powerPotential (ell : ℕ) (a : ℝ) :
    Continuous (powerPotential ell a) := by
  exact ((continuous_id.pow _).sub (continuous_const.mul continuous_id)).add continuous_const

theorem continuous_separatedPotential {n : ℕ} (ell : ℕ) (a : Fin n → ℝ) :
    Continuous (separatedPotential ell a) :=
  continuous_finsetSum _ (fun i _ => (continuous_powerPotential ell (a i)).comp (continuous_apply i))

theorem separatedPotential_coordinate_bound {n : ℕ} (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ separatedPotential ell a x + (ell + 1 : ℕ) * a i ^ ell + 1 := by
  have hcoord : powerPotential ell (a i) (x i) ≤ separatedPotential ell a x :=
    Finset.single_le_sum (fun j _ => (pow_nonneg (ha j) _).trans
      (powerPotential_lower ell he (a j) (x j) (ha j))) (Finset.mem_univ i)
  have hbound := abs_le_powerPotential ell hell he (a i) (x i) (ha i)
  linarith

/-- Every sublevel of the actual separated potential is compact,
 with an explicit coordinate box. This includes zero variables. -/
theorem separatedPotential_compact_sublevel {n : ℕ} (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (B : ℝ) :
    IsCompact {x : Fin n → ℝ | separatedPotential ell a x ≤ B} := by
  have hclosed : IsClosed {x : Fin n → ℝ | separatedPotential ell a x ≤ B} :=
    isClosed_le (continuous_separatedPotential ell a) continuous_const
  apply (isCompact_Icc : IsCompact
    (Icc (fun i : Fin n => -(B + (ell + 1 : ℕ) * a i ^ ell + 1))
      (fun i => B + (ell + 1 : ℕ) * a i ^ ell + 1))).of_isClosed_subset hclosed
  intro x hx
  change separatedPotential ell a x ≤ B at hx
  constructor <;> intro i
  · have hb := separatedPotential_coordinate_bound ell hell he a ha x i
    exact (abs_le.mp (by linarith : |x i| ≤ B + (ell + 1 : ℕ) * a i ^ ell + 1)).1
  · have hb := separatedPotential_coordinate_bound ell hell he a ha x i
    exact (abs_le.mp (by linarith : |x i| ≤ B + (ell + 1 : ℕ) * a i ^ ell + 1)).2

end LeanCanny.CountingHierarchy
