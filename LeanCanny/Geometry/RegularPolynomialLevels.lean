/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialCriticalValues
import Mathlib.Tactic.Linarith

/-! # Regular sufficiently small positive levels of a real polynomial

Finitely many critical values give a positive margin below every positive
critical value. All levels within that margin have surjective derivatives.
The margin is existential and has no effective size bound here.
-/

@[expose] public section

namespace LeanCanny.Geometry.RegularPolynomialLevels

theorem surjective_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] ℝ) (hD : D ≠ 0) : Function.Surjective D := by
  obtain ⟨h, hh⟩ := DFunLike.ne_iff.mp hD
  have hne : D h ≠ 0 := by simpa only [zero_apply] using hh
  intro y
  refine ⟨(y / D h) • h, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]

theorem exists_interval {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a → ∀ x : ι → ℝ,
      MvPolynomial.aeval x p = alpha →
        Function.Surjective (fderiv ℝ (fun y => MvPolynomial.aeval y p - alpha) x) := by
  classical
  let C : Set ℝ := {c | ∃ x : ι → ℝ,
    fderiv ℝ (fun y => MvPolynomial.aeval y p) x = 0 ∧ MvPolynomial.aeval x p = c}
  have hC : C.Finite := PolynomialCalculus.finite_critical_values p
  let positive := hC.toFinset.filter (fun c => 0 < c)
  obtain ⟨a, ha, hm⟩ := CubeCoordinates.finite_positive_margin positive id (by
    intro c hc
    exact (Finset.mem_filter.mp hc).2)
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs x hx
  rw [fderiv_sub_const]
  apply surjective_of_ne_zero
  intro hzero
  have hc : alpha ∈ C := ⟨x, hzero, hx⟩
  have hpos : alpha ∈ positive := Finset.mem_filter.mpr ⟨hC.mem_toFinset.mpr hc, hp⟩
  have hbound : a ≤ alpha := hm alpha hpos
  exact (not_lt_of_ge hbound) hs

end LeanCanny.Geometry.RegularPolynomialLevels
