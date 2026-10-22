/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialCriticalValues
public import LeanCanny.Geometry.ActiveRadiusCritical
import Mathlib.Tactic.Linarith

/-! # A common interval of regular perturbation radii

The finitely many active sets have finitely many critical energy values. A
positive margin below their positive values gives a common interval of radii
where every active augmented derivative is surjective. The interval is
existential: no effective lower bound is supplied here.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation

variable {ι : Type*} [Fintype ι]

theorem exists_regular_interval (p : MvPolynomial ι ℤ) (epsilon : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      ∀ (s : Finset (Constraint ι)) (z : (ι → ℝ) × (Constraint ι → ℝ)),
        (∀ i ∈ s, parameterMap p epsilon z i = 0) → SquaredRadius.value z.2 = delta ^ 2 →
          Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap (constraintMap p epsilon) s delta) z) := by
  classical
  let C : Set ℝ := ⋃ s : Finset (Constraint ι),
    {c | ∃ x : ι → ℝ, fderiv ℝ (ActiveRadius.energy (constraintMap p epsilon) s) x = 0 ∧
      ActiveRadius.energy (constraintMap p epsilon) s x = c}
  have hC : C.Finite := Set.finite_iUnion (fun s => finite_energy_critical_values p s epsilon)
  let positive := hC.toFinset.filter (fun c => 0 < c)
  obtain ⟨d, hd, hm⟩ := CubeCoordinates.finite_positive_margin positive id (by
    intro c hc
    exact (Finset.mem_filter.mp hc).2)
  refine ⟨min d 1, lt_min hd (by norm_num), ?_⟩
  intro delta hdelta hsmall s z ha hr
  by_contra hs
  have hf := ((contDiff_constraintMap p epsilon).differentiable (by simp)) z.1
  obtain ⟨hv, hc⟩ := ActiveRadius.singular_implies_critical (constraintMap p epsilon) s delta z hf ha hr hs
  have hmC : delta ^ 2 ∈ C := Set.mem_iUnion.mpr ⟨s, z.1, hc, hv⟩
  have hpos : delta ^ 2 ∈ positive := Finset.mem_filter.mpr
    ⟨hC.mem_toFinset.mpr hmC, sq_pos_of_pos hdelta⟩
  have hbound : d ≤ delta ^ 2 := hm _ hpos
  have hdelta_one : delta < 1 := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hdelta_d : delta < d := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hsquare : delta ^ 2 < delta := by nlinarith
  exact (not_lt_of_ge hbound) (hsquare.trans hdelta_d)

end LeanCanny.Geometry.PolynomialPerturbation
