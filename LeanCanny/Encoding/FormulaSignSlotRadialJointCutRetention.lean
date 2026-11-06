/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointBranchCutRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialJointValueIntervalRetention
public import LeanCanny.Connectivity.FormulaSignSlotRadialBranchCuts
/-! # All four actual radial cut classes and one fresh joint sampler word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCutRetention
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "Space" => FormulaSignSlotRadialJointStratumLabels.Space
noncomputable abbrev root := FormulaSignSlotRadialJointHeadIntervalRetention.root
noncomputable def CutFree (c : List Bool) (x : Space c) : Prop := ∀ r ∈ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x),
  r ∉ FormulaSignSlotRadialBranchCuts.cuts (root c) (FormulaSignSlotRadialJointDescriptorGeometry.center c x)
private def NoRoot (p : ℝ[X]) (b : ℝ) : Prop := ∀ r, p.eval r=0 → r ∉ Ioo 0 b

private theorem no_cuts_iff (u : List Bool) (a : Fin (FormulaSignSlotCenteredRadialGraph.d u) → ℝ) (b : ℝ) :
    (∀ r ∈ Ioo 0 b, r ∉ FormulaSignSlotRadialBranchCuts.cuts u a) ↔
    (∀ j, NoRoot (FormulaSignSlotRadialParameterEliminant.coordinate u a j).leadingCoeff b) ∧
    (∀ r ∈ Ioo 0 b, r ∉ RealParameterRootBranches.bad (FormulaSignSlotRadialParameterEliminant.coordinate u a)) ∧
    NoRoot (FormulaSignSlotRadialValueCertificate.polynomial u a).trailingCoeff b ∧
    NoRoot (FormulaSignSlotRadialParameterEliminant.coordinate u a (FormulaSignSlotCenteredRadialGraph.marginIndex u)).trailingCoeff b := by
  constructor
  · intro H
    refine ⟨?_,?_,?_,?_⟩
    · intro j r hz hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).1 ⟨j,hz⟩
    · intro r hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).2.1
    · intro r hz hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).2.2.1 hz
    · intro r hz hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).2.2.2 hz
  · rintro ⟨HL,HB,HV,HM⟩ r hr hbad
    unfold FormulaSignSlotRadialBranchCuts.cuts at hbad
    rcases hbad with ((hL|hB)|hV)|hM
    · obtain ⟨j,hz⟩ := hL
      exact HL j r hz hr
    · exact HB r hr hB
    · exact HV r hV hr
    · exact HM r hM hr

attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialParameterEliminant.coordinate
  FormulaSignSlotRadialValueCertificate.polynomial

/-- Actual leading, squarefree-branch, value and margin cuts share one source point. -/
theorem cut_free_iff_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val) :
    CutFree c x ↔ CutFree c y := by
  unfold CutFree
  rw [no_cuts_iff,no_cuts_iff]
  apply and_congr
  · exact forall_congr' fun j => FormulaSignSlotRadialJointHeadIntervalRetention.actual_leading_interval_iff_of_joined c x y h j
  · apply and_congr
    · exact FormulaSignSlotRadialJointBranchCutRetention.bad_interval_iff_of_joined c x y h
    · apply and_congr
      · exact FormulaSignSlotRadialJointValueIntervalRetention.actual_interval_iff_of_joined c x y h
      · exact FormulaSignSlotRadialJointHeadIntervalRetention.actual_trailing_interval_iff_of_joined c x y h
          (FormulaSignSlotCenteredRadialGraph.marginIndex (root c))

/-- One fresh Gamma and OWN word retain both original labels, the actual grid
and every cut class on the same complete sampler tuple. -/
theorem component_hit (c : List Bool) (x : Space c)
    (hLabels : FormulaSignSlotRadialJointStratumLabels.BothLabels c x)
    (hGrid : FormulaSignSlotRadialJointGridRetention.Grid c x) (hCuts : CutFree c x) :
    ∃ Gamma : List Bool, Gamma.length ≤ FormulaSignSlotRadialJointStratumSampler.tableBound c ∧
      ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) w),
        w.length = SquareSampleCompleteVertices.width FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) ∧
        w.length ≤ FormulaSignSlotRadialJointStratumSampler.ownwordBound c ∧
        pair (pair c Gamma) w ∈ FormulaSignSlotRadialJointStratumSampler.language ∧
        ∃ a : Space c,
          JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val a.val ∧
          FormulaSignSlotRadialJointStratumLabels.BothLabels c a ∧
          FormulaSignSlotRadialJointGridRetention.Grid c a ∧ CutFree c a ∧
          HEq (SquareSampleCompleteVertices.candidate FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) w hw).val a.val := by
  obtain ⟨Gamma,hGamma,w,hw,hlen,hbound,hq,a,hpath,hGa,hpoint⟩ :=
    FormulaSignSlotRadialJointGridRetention.component_hit_grid c x hGrid
  exact ⟨Gamma,hGamma,w,hw,hlen,hbound,hq,a,hpath,
    (FormulaSignSlotRadialJointStratumLabels.bothLabels_iff c x a hpath).mp hLabels,
    hGa,(cut_free_iff_of_joined c x a hpath).mp hCuts,hpoint⟩

end LeanCanny.Encoding.FormulaSignSlotRadialJointCutRetention
