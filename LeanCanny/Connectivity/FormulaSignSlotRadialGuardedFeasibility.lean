/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointWitnessReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCutRetention
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointFeasibility
/-! # Exact bounded shared-word feasibility with all original guards

The word predicate below retains literal interval-cut semantics. Its native
interval decision cost is a separate obligation; no PSPACE claim is made here.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibility
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "env" => FormulaSignSlotRadialImplicitGridTest.env
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialJointStratum.source ImplicitSourceGramGrid.input
  SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate FormulaSignSlotRadialParameterGrid.grid


noncomputable def PointCuts (H : List Bool) (v : ℕ → ℝ) : Prop :=
  ∀ r ∈ Ioo 0 (v FormulaSignSlotRadialJointLayout.boundVariable),
    r ∉ FormulaSignSlotRadialBranchCuts.cuts (FormulaSignSlotRadialJointLayout.source true H)
      (FormulaSignSlotRadialJointGeometry.center H v)
noncomputable def OwnGood (cc w : List Bool) : Prop :=
  pair cc w ∈ FormulaSignSlotRadialJointStratumSampler.language ∧
  ∃ hw : SquareSampleCompleteVertices.Valid F cc w,
    FormulaSignSlotRadialImplicitGridSelection.Holds (pair cc w) ∧
    PointCuts (FormulaSignSlotRadialImplicitGridTest.header cc) (env cc w hw)
noncomputable def wordLanguage : Language := {p | OwnGood (pairFst p) (pairSnd p)}

private theorem word_packet (cc w : List Bool) : pair cc w ∈ wordLanguage ↔ OwnGood cc w := by
  simp only [wordLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]

private theorem radial_grid_iff (q : List Bool) (v : ℕ → ℝ)
    (hv : (FormulaSignSlotRadialJointCore.equation q).eval v = 0) :
    (FormulaSignSlotRadialJointGeometry.radialPoint q v hv).val.val ∈
      FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointLayout.source true q)
        (FormulaSignSlotRadialJointGeometry.center q v) (FormulaSignSlotRadialJointGeometry.parameter q v) ↔
    FormulaSignSlotRadialJointGeometry.spatialPoint q v ∈
      FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointLayout.source true q)
        (FormulaSignSlotRadialJointGeometry.center q v) (FormulaSignSlotRadialJointGeometry.parameter q v) := Iff.rfl

private theorem anchor_grid_iff (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    FormulaSignSlotRadialJointGridRetention.Grid c x ↔
      (FormulaSignSlotRadialJointDescriptorGeometry.anchor c x).val.val ∈
        FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointStratumLabels.source true c)
          (FormulaSignSlotRadialJointDescriptorGeometry.center c x) (FormulaSignSlotRadialJointDescriptorGeometry.radius c x) := by
  exact (radial_grid_iff _ _ (FormulaSignSlotRadialJointDescriptorGeometry.core_zero c x)).symm

/-- The checked word and the actual point use exactly the same grid, center,
bound and all four cut classes. -/
theorem word_iff (c Gamma w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (hq : pair (pair c Gamma) w ∈ FormulaSignSlotRadialJointStratumSampler.language)
    (x : FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx : HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val) :
    pair (pair c Gamma) w ∈ wordLanguage ↔
      FormulaSignSlotRadialJointGridRetention.Grid c x ∧ FormulaSignSlotRadialJointCutRetention.CutFree c x := by
  have HH : FormulaSignSlotRadialImplicitGridTest.header (pair c Gamma) = FormulaSignSlotRadialJointStratum.header c := by
    simp only [FormulaSignSlotRadialImplicitGridTest.header,ImplicitSourceGramGrid.header,pairFst_pair]
  rw [word_packet]
  simp only [OwnGood,HH]
  constructor
  · rintro ⟨_HQ,hw',HG,HC⟩
    have HC0 : PointCuts (FormulaSignSlotRadialJointStratum.header c) (env (pair c Gamma) w hw) := by
      simpa only using HC
    refine ⟨(FormulaSignSlotRadialImplicitSampleReadback.grid_iff c Gamma w hw x hx).mp HG,?_⟩
    exact (FormulaSignSlotRadialImplicitSampleReadback.cut_free_iff c Gamma w hw x hx).mp HC0
  · rintro ⟨HG,HC⟩
    have HC0 : PointCuts (FormulaSignSlotRadialJointStratum.header c) (env (pair c Gamma) w hw) :=
      (FormulaSignSlotRadialImplicitSampleReadback.cut_free_iff c Gamma w hw x hx).mpr HC
    refine ⟨hq,hw,(FormulaSignSlotRadialImplicitSampleReadback.grid_iff c Gamma w hw x hx).mpr HG,?_⟩
    simpa only using HC0

noncomputable def language : Language := FormulaSignSlotRadialProviderGuardedJointWitness.language wordLanguage

/-- The bounded two-label certificate with all guards is exactly the original
geometric joint feasibility predicate. Every budget is constructed internally. -/
theorem language_iff_feasible (H : List Bool) :
    H ∈ language ↔ FormulaSignSlotRadialJointFeasibility.Feasible H := by
  rw [language,FormulaSignSlotRadialProviderGuardedJointWitness.language_iff]
  constructor
  · rintro ⟨k,Gamma,w,aL,eL,aR,eR,HW,HG⟩
    obtain ⟨hw,x,HB,hx⟩ := FormulaSignSlotRadialProviderJointWitnessReadback.point_of_witness H k Gamma w aL eL aR eR HW
    have HC := (word_iff _ Gamma w hw HW.2.2.1 x hx).mp HG
    exact ⟨k,x,HB,(anchor_grid_iff _ x).mp HC.1,HC.2⟩
  · rintro ⟨k,x,HB,HG,HC⟩
    obtain ⟨Gamma,hGamma,w,hw,_HL,_HB,hq,a,_HP,HA,HGa,HCa,hx⟩ :=
      FormulaSignSlotRadialJointCutRetention.component_hit _ x HB ((anchor_grid_iff _ x).mpr HG) HC
    obtain ⟨aL,eL,aR,eR,HW⟩ := FormulaSignSlotRadialProviderJointSampleWitness.witness_of_sampled_point H k Gamma w hGamma hw hq a hx HA
    exact ⟨k,Gamma,w,aL,eL,aR,eR,HW,(word_iff _ Gamma w hw hq a hx).mpr ⟨HGa,HCa⟩⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibility
