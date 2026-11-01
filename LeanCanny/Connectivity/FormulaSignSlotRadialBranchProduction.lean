/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialBranchSelection
/-! # Actual positive branches approaching a specified sign-piece boundary

Compact singular slice sampling, one uniform perturbation-limit family, finite
coefficient cuts, squarefree continuation and Gram pruning are combined here.
The resulting branch stays in the selected old positive piece and its literal
old-coordinate squared distance equals the parameter. No regularity or branch
existence premise is supplied, and no auxiliary endpoint root is lifted.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialBranchProduction
open ETR Set Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits FormulaSignSlotRadialParameterEliminant
open FormulaSignSlotRadialBranchCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

theorem exists_positive_branch (c : List Bool) (C : Set (Positive c)) (hC : IsClopen C)
    (x : Source c) (hx : x∈closure (ambient c C)) (hn : x∉ambient c C) :
    ∃ b : ℝ, 0 < b ∧ ∃ _t₀ : Ioo (0 : ℝ) b, ∃ f : C(Ioo (0 : ℝ) b, Positive c),
      (∀ t, f t∈C) ∧
      ∀ t, SquaredDistanceFibers.value (projection c x).val (projection c (f t).val).val=t.val := by
  obtain ⟨r₀,_HR₀,_HL₀,HB₀,z₀,_HC₀,HG₀,_HS₀⟩ :=
    FormulaSignSlotRadialParameterGrid.arbitrarily_small_samples c C hC x hx hn 1 zero_lt_one
  obtain ⟨b,hb,HB⟩ := small_interval c (projection c x).val r₀ HB₀ z₀.val.val HG₀
  obtain ⟨r,hr,hl,_HR,z,HZ,HG,_HS⟩ :=
    FormulaSignSlotRadialParameterGrid.arbitrarily_small_samples c C hC x hx hn b hb
  let t₀ : Ioo (0 : ℝ) b := ⟨r,hr,hl⟩
  obtain ⟨_HF,curve,_HA,Hgrid,Hcomplete⟩ := branches c (projection c x).val b t₀ HB
  obtain ⟨j,HJ,_HU⟩ := (Hcomplete t₀ z.val.val).mp HG
  obtain ⟨f,HA,HD⟩ := FormulaSignSlotRadialBranchSelection.selected_curve c (projection c x).val b HB t₀ z
    (curve j) HJ (Hgrid j)
  let : PreconnectedSpace (Ioo (0 : ℝ) b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have HC₀ : f t₀∈C := by rw [HA]; exact HZ
  have HC := (isPreconnected_range f.continuous).subset_isClopen hC ⟨f t₀,⟨t₀,rfl⟩,HC₀⟩
  exact ⟨b,hb,t₀,f,(fun t => HC ⟨t,rfl⟩),HD⟩
end LeanCanny.Connectivity.FormulaSignSlotRadialBranchProduction
