/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialBranchCuts
/-! # One actual positive sample selects an entire radial source branch -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialBranchSelection
open ETR Set Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits FormulaSignSlotRadialParameterEliminant
open FormulaSignSlotRadialBranchCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
theorem forget_continuous (c : List Bool) : Continuous (forget c) :=
  CenteredRadialGraph.oldPoint_continuous _ _ _ (FormulaSignSlotCenteredRadialGraph.scope c)

attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

theorem selected_curve (c : List Bool) (a : Fin (d c) → ℝ) (b : ℝ)
    (hcut : ∀ t∈Ioo 0 b, t∉cuts c a) (t₀ : Ioo (0 : ℝ) b)
    (z : FormulaSignSlotTiltedRadialGrid.OldPositive c a t₀.val)
    (curve : C(Ioo (0 : ℝ) b, Fin (N c+d c+1) → ℝ))
    (hanchor : curve t₀=z.val.val)
    (hgrid : ∀ t, curve t∈FormulaSignSlotRadialParameterGrid.grid c a t.val) :
    ∃ f : C(Ioo (0 : ℝ) b, Positive c),
      f t₀=FormulaSignSlotTiltedRadialGrid.originalPositive c a t₀.val z ∧
      ∀ t, SquaredDistanceFibers.value a (projection c (f t).val).val=t.val := by
  let : PreconnectedSpace (Ioo (0 : ℝ) b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have HQ₀ : (FormulaSignSlotCenteredRadialLimits.polynomial c a t₀.val).eval (curve t₀)=0 := by
    rw [hanchor]
    exact z.val.property
  have HQ (t : Ioo (0 : ℝ) b) : (FormulaSignSlotCenteredRadialLimits.polynomial c a t.val).eval (curve t)=0 :=
    (FormulaSignSlotRadialValueCertificate.slice_zero_iff c a (fun t : Ioo (0 : ℝ) b => t.val) curve
      continuous_subtype_val curve.continuous hgrid
      (fun t => (conditions c a _ (hcut _ t.property)).2.2.1) t₀ t).mp HQ₀
  have HU (t : Ioo (0 : ℝ) b) : 0 < curve t (marginIndex c) := by
    have H := (AlgebraicBranchSign.sign_iff (coordinate c a (marginIndex c))
      (fun t : Ioo (0 : ℝ) b => t.val) (fun t => curve t (marginIndex c)) continuous_subtype_val
      ((continuous_apply _).comp curve.continuous) (fun t => hgrid t (marginIndex c))
      (fun t => (conditions c a _ (hcut _ t.property)).2.2.2) t₀ t).2
    apply H.mp
    rw [hanchor]
    exact z.property
  let G : Ioo (0 : ℝ) b → Graph c := fun t => ⟨curve t,(FormulaSignSlotCenteredRadialLimits.zero_iff c a t.val _).mp (HQ t) |>.1⟩
  have HG : Continuous G := curve.continuous.subtype_mk _
  let f : Ioo (0 : ℝ) b → Positive c := fun t => ⟨forget c (G t),by rw [← margin_coordinate]; exact HU t⟩
  have Hforget : Continuous (fun t : Ioo (0 : ℝ) b => forget c (G t)) :=
    (forget_continuous c).comp HG
  have HF : Continuous f := Hforget.subtype_mk _
  refine ⟨⟨f,HF⟩,?_,?_⟩
  · apply Subtype.ext
    change forget c (G t₀)=forget c (FormulaSignSlotTiltedRadialGrid.zeroPoint c a t₀.val z.val)
    apply congrArg (forget c)
    exact Subtype.ext hanchor
  · intro t
    exact forget_slice c a t.val ((FormulaSignSlotCenteredRadialLimits.zero_iff c a t.val _).mp (HQ t)).2
end LeanCanny.Connectivity.FormulaSignSlotRadialBranchSelection
