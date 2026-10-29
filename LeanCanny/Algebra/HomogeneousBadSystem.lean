/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveCriticalHomogenization
public import LeanCanny.Algebra.PolynomialMapDegree

/-! # Homogenizing a system together with its bad-root polynomial

Original roots avoid the bad-root polynomial in the affine chart. If the
original homogeneous equations have no root at infinity, appending the
homogenized bad-root polynomial gives a projectively root-free square system.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogeneousBadSystem
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {σ R K : Type*} [Fintype σ] [CommRing R] [Field K]

def degrees (d : σ → ℕ) (B : ℕ) : Option σ → ℕ := fun i => i.elim B d

noncomputable def rows (p : σ → MvPolynomial σ R) (d : σ → ℕ)
    (J : MvPolynomial σ R) (B : ℕ) : Option σ → MvPolynomial (Option σ) R
  | none => homogenize (fun _ => 1) B J
  | some i => homogenize (fun _ => 1) (d i) (p i)

theorem homogeneous (p : σ → MvPolynomial σ R) (d : σ → ℕ)
    (J : MvPolynomial σ R) (B : ℕ) (i : Option σ) :
    (rows p d J B i).IsHomogeneous (degrees d B i) := by
  have hw : weights (fun _ : σ => 1) = 1 := by funext j; cases j <;> rfl
  cases i <;> simpa only [rows, degrees, Option.elim_none, Option.elim_some, IsHomogeneous, hw] using
    WeightedHomogenization.homogeneous (fun _ : σ => 1) _ _

theorem chart_root (φ : R →+* K) (p : σ → MvPolynomial σ R) (d : σ → ℕ)
    (J : MvPolynomial σ R) (B : ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (hJ : J.totalDegree ≤ B)
    (x : σ → K) (hx : ∀ i, (p i).eval₂ φ x = 0) (hxJ : J.eval₂ φ x = 0)
    (i : Option σ) : (rows p d J B i).eval₂ φ (fun j => j.elim 1 x) = 0 := by
  cases i with
  | none =>
    rw [rows, WeightedHomogenization.eval_chart]
    · exact hxJ
    · intro e he
      exact (weight_le_degree (fun _ => 1) (by simp) e).trans ((le_totalDegree he).trans hJ)
  | some i =>
    rw [rows, WeightedHomogenization.eval_chart]
    · exact hx i
    · intro e he
      exact (weight_le_degree (fun _ => 1) (by simp) e).trans ((le_totalDegree he).trans (hp i))

/-- Affine regularity and exclusion at infinity suffice; the coefficient map
can have a kernel and the target field need not be algebraically closed. -/
theorem no_nonzero_root (φ : R →+* K)
    (p : σ → MvPolynomial σ R) (d : σ → ℕ)
    (J : MvPolynomial σ R) (B : ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (hJ : J.totalDegree ≤ B)
    (haffine : ∀ x : σ → K, (∀ i, (p i).eval₂ φ x = 0) → J.eval₂ φ x ≠ 0)
    (hinfinity : ∀ y : Option σ → K, y none = 0 →
      (∀ i, (rows p d J B (some i)).eval₂ φ y = 0) → y = 0)
    (y : Option σ → K) (hy : ∀ i, (rows p d J B i).eval₂ φ y = 0) : y = 0 := by
  by_cases hy0 : y none = 0
  · exact hinfinity y hy0 (fun i => hy (some i))
  · exfalso
    let x : σ → K := fun i => (y none)⁻¹ * y (some i)
    have hchart : (fun i : Option σ => (y none)⁻¹ * y i) = fun i => i.elim 1 x := by
      funext i
      cases i with
      | none => exact inv_mul_cancel₀ hy0
      | some i => rfl
    have hn (i : Option σ) : (rows p d J B i).eval₂ φ (fun j => j.elim 1 x) = 0 := by
      rw [← hchart, ← eval_map]
      rw [CoerciveCriticalHomogenization.eval_scale _ _ ((homogeneous p d J B i).map φ), eval_map, hy i, mul_zero]
    have hx (i : σ) : (p i).eval₂ φ x = 0 := by
      have h := hn (some i)
      rw [rows, WeightedHomogenization.eval_chart] at h
      · exact h
      · intro e he
        exact (weight_le_degree (fun _ => 1) (by simp) e).trans ((le_totalDegree he).trans (hp i))
    have hzero : J.eval₂ φ x = 0 := by
      have h := hn none
      rw [rows, WeightedHomogenization.eval_chart] at h
      · exact h
      · intro e he
        exact (weight_le_degree (fun _ => 1) (by simp) e).trans ((le_totalDegree he).trans hJ)
    exact haffine x hx hzero

end LeanCanny.Algebra.HomogeneousBadSystem
