/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCoordinateCone

/-! # Independence of nonzero scaled coordinate normals -/

@[expose] public section
namespace LeanCanny.Geometry.ScaledCoordinateIndependence
open LeanCanny.Algebra
open scoped Classical BigOperators

theorem normals {n : ℕ} (s : Finset (Fin n)) (scale : Fin n → ℝ) (hscale : ∀ i, scale i ≠ 0) :
    ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * (scale j.val * FermatCoordinateCone.normal j.val i) = 0) → ∀ j, c j = 0 := by
  intro c hc r
  have HS : (∑ j : s, c j * (scale j.val * FermatCoordinateCone.normal j.val r.val)) = c r * scale r.val := by
    rw [Finset.sum_eq_single r]
    · simp only [FermatCoordinateCone.normal, ite_true, mul_one]
    · intro j _ hj
      have HJ : r.val ≠ j.val := fun he => hj (Subtype.ext he.symm)
      simp only [FermatCoordinateCone.normal, HJ, ite_false, mul_zero]
    · intro H
      exact False.elim (H (Finset.mem_univ r))
  exact (mul_eq_zero.mp (HS.symm.trans (hc r.val))).resolve_right (hscale r.val)

theorem objective {n : ℕ} (s : Finset (Fin n)) (scale : Fin n → ℝ)
    (r : Fin n) (hr : r ∉ s) (b : ℝ) (hb : b ≠ 0) :
    ¬∃ c : s → ℝ, ∀ i, b * FermatCoordinateCone.normal r i =
      ∑ j : s, c j * (scale j.val * FermatCoordinateCone.normal j.val i) := by
  rintro ⟨c, hc⟩
  have HS : (∑ j : s, c j * (scale j.val * FermatCoordinateCone.normal j.val r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have HJ : r ≠ j.val := fun he => hr (he.symm ▸ j.property)
    simp only [FermatCoordinateCone.normal, HJ, ite_false, mul_zero]
  have H : b = 0 := by simpa only [FermatCoordinateCone.normal, ite_true, mul_one] using (hc r).trans HS
  exact hb H

end LeanCanny.Geometry.ScaledCoordinateIndependence
