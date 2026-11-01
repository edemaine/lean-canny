/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialParameterEliminant
/-! # Uniform radius equations capture the actual positive radial samples

One explicit finite coefficient-root set suffices for lowest-perturbation
specialization. Arbitrarily small same-piece samples satisfy the single
constructed parameter family, with no threshold or evaluator premise.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialParameterGrid
open ETR Set Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits FormulaSignSlotRadialParameterEliminant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

noncomputable def grid (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) : Set (Fin (N c+d c+1) → ℝ) :=
  {x | ∀ i, (coordinate c a i).eval₂ (Polynomial.evalRingHom r) (x i)=0}

theorem grid_iff (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : r∉bad c a)
    (x : Fin (N c+d c+1) → ℝ) : x∈grid c a r ↔ x∈FormulaSignSlotTiltedRadialGrid.grid c a r := by
  change (∀ i, (coordinate c a i).eval₂ (Polynomial.evalRingHom r) (x i)=0) ↔ _
  simp only [FormulaSignSlotTiltedRadialGrid.grid,FormulaSignSlotTiltedRadialGrid.Q,
    TiltedCoerciveComponentEliminants.grid,mem_ofPred_eq]
  apply forall_congr'
  intro i
  rw [← Polynomial.eval_map,coordinate_specialization c a r hr i]

theorem finite_grid (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : r∉bad c a) : (grid c a r).Finite :=
  (FormulaSignSlotTiltedRadialGrid.finite_grid c a r).subset (fun x hx => (grid_iff c a r hr x).mp hx)

theorem sample_same_piece (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : 0≤r) (hb : r∉bad c a)
    (C : Set (Positive c)) (hC : IsClopen C) (x : Positive c) (hxC : x∈C)
    (hx : x.val∈sourceSphere c a r) :
    ∃ z : FormulaSignSlotTiltedRadialGrid.OldPositive c a r,
      FormulaSignSlotTiltedRadialGrid.originalPositive c a r z∈C ∧
      value c x.val≤z.val.val (marginIndex c) ∧ z.val.val∈grid c a r := by
  obtain ⟨z,HZ,HU,HG⟩ := FormulaSignSlotTiltedRadialGrid.sample_same_piece c a r hr C hC x hxC hx
  exact ⟨z,HZ,HU,(grid_iff c a r hb z.val.val).mpr HG⟩

theorem small_interval (c : List Bool) (a : Fin (d c) → ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ r∈Ioo 0 b, r∉bad c a := by
  obtain ⟨l,b,hl,hb,HI⟩ := CoerciveConstrainedSampling.exists_isolating_interval (bad c a) (finite_bad c a) 0
  refine ⟨b,hb,?_⟩
  intro r hr hbad
  exact (ne_of_gt hr.1) (HI r hbad ⟨hl.le.trans hr.1.le,hr.2.le⟩)

theorem arbitrarily_small_samples (c : List Bool) (C : Set (Positive c)) (hC : IsClopen C)
    (x : Source c) (hx : x∈closure (ambient c C)) (hn : x∉ambient c C) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ r∉bad c (projection c x).val ∧
      ∃ z : FormulaSignSlotTiltedRadialGrid.OldPositive c (projection c x).val r,
        FormulaSignSlotTiltedRadialGrid.originalPositive c (projection c x).val r z∈C ∧
        z.val.val∈grid c (projection c x).val r ∧
        (FormulaSignSlotTiltedRadialGrid.originalPositive c (projection c x).val r z).val∈
          sourceSphere c (projection c x).val r := by
  obtain ⟨b,hb,HB⟩ := small_interval c (projection c x).val
  obtain ⟨r,hr,hη,z,HZ,HG,HS⟩ := FormulaSignSlotTiltedRadialGrid.arbitrarily_small_samples
    c C hC x hx hn (min ε b) (lt_min hε hb)
  have Hrb : r∉bad c (projection c x).val := HB r ⟨hr,hη.trans_le (min_le_right _ _)⟩
  exact ⟨r,hr,hη.trans_le (min_le_left _ _),Hrb,z,HZ,
    (grid_iff c (projection c x).val r Hrb z.val.val).mpr HG,HS⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialParameterGrid
