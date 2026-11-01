/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCenteredRadialLimits
public import LeanCanny.Geometry.CoerciveComponentEliminants
/-! # Finite actual coordinate samples of each compact singular radial fiber -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGrid
open Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical

noncomputable def grid (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :=
  CoerciveComponentEliminants.grid (polynomial c a r) (degreeBudget c)

theorem finite_grid (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) : (grid c a r).Finite :=
  CoerciveComponentEliminants.finite_grid _ _ (polynomial_degree c a r)

theorem meets_piece (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : 0≤r)
    (S : Set (CoerciveComponentSampling.Zeros (polynomial c a r))) (hS : IsClopen S)
    (x0 : CoerciveComponentSampling.Zeros (polynomial c a r)) (hx0 : x0∈S) :
    ∃ z : CoerciveComponentSampling.Zeros (polynomial c a r), z∈S ∧ z.val∈grid c a r :=
  CoerciveComponentEliminants.meets_piece _ _ (polynomial_degree c a r)
    (compact_zeros c a r hr) S hS x0 hx0

end LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGrid
