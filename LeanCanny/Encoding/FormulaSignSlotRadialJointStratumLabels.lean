/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler
public import LeanCanny.Encoding.FormulaSignSlotRadialJointComponentTransport
/-! # The implicit sampler retains both prescribed closed-source labels

Component membership is defined using the two labels in the original joint
packet. A path in the actual stratum preserves both labels simultaneously.
The bounded own-word theorem therefore applies inside their intersection.
Native evaluation of these component predicates is a separate obligation.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source

noncomputable abbrev Space (c : List Bool) := Zeros (((S).polynomial c).map (Int.castRingHom ℝ))
noncomputable def source (side : Bool) (c : List Bool) :=
  FormulaSignSlotRadialJointLayout.source side (FormulaSignSlotRadialJointStratum.header c)
noncomputable def label (side : Bool) (c : List Bool) := CanonicalAuxiliaryCandidateLabels.candidate
  (FormulaSignSlotRadialJointLayout.labelQuery side (FormulaSignSlotRadialJointStratum.header c))

def Good (side : Bool) (c : List Bool) : Prop := AuxiliaryCandidateComponentCover.Good
  CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
  CanonicalAuxiliaryCandidateCover.equation_scope (source side c) (label side c)

noncomputable def sample (side : Bool) (c : List Bool) (h : Good side c) :
    FormulaSignSlotCircularBoundedCover.Source (source side c) :=
  (CanonicalAuxiliaryCandidateCover.sourceHomeomorph (source side c)).symm
    ⟨IntegralMixedAuxiliaryCandidate.pointAt CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
      (source side c) (label side c) (Classical.choose h),
      (AuxiliaryCandidateComponentCover.evaluation _ _ _).trans (Classical.choose_spec h)⟩

theorem source_zero (c : List Bool) (x : Space c) :
    ((S).polynomial c).eval₂ (Int.castRingHom ℝ) x.val = 0 := by
  have hx := x.property
  change MvPolynomial.eval x.val (((S).polynomial c).map (Int.castRingHom ℝ)) = 0 at hx
  simpa only [MvPolynomial.eval_map] using hx

noncomputable def corePoint (c : List Bool) (x : Space c) :
    AuxiliaryCandidateComponentCover.Space FormulaSignSlotRadialJointLayout.dimension
      FormulaSignSlotRadialJointCore.equation (FormulaSignSlotRadialJointStratum.header c) :=
  ⟨FormulaSignSlotRadialJointStratum.oldPoint c x.val,
    (AuxiliaryCandidateComponentCover.evaluation _ _ _).trans
      (((FormulaSignSlotRadialJointStratum.zero_iff c x.val).mp (source_zero c x)).1)⟩

theorem continuous_corePoint (c : List Bool) : Continuous (corePoint c) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply i.castSucc).comp continuous_subtype_val

noncomputable def project (side : Bool) (c : List Bool) (x : Space c) :
    FormulaSignSlotCircularBoundedCover.Source (source side c) :=
  FormulaSignSlotRadialJointComponentTransport.project side (FormulaSignSlotRadialJointStratum.header c)
    (corePoint c x)

theorem continuous_project (side : Bool) (c : List Bool) : Continuous (project side c) :=
  (FormulaSignSlotRadialJointComponentTransport.continuous_project side
    (FormulaSignSlotRadialJointStratum.header c)).comp (continuous_corePoint c)

theorem joined_project (side : Bool) (c : List Bool) (x y : Space c)
    (h : JoinedIn (Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val) :
    JoinedIn Set.univ (project side c x) (project side c y) :=
  joinedIn_univ.mpr (((joinedIn_iff_joined x.property y.property).mp h).map (continuous_project side c))

noncomputable def AtLabel (side : Bool) (c : List Bool) (x : Space c) : Prop :=
  ∃ hg : Good side c, JoinedIn Set.univ (sample side c hg) (project side c x)

noncomputable def BothLabels (c : List Bool) (x : Space c) : Prop := ∀ side, AtLabel side c x

theorem atLabel_iff (side : Bool) (c : List Bool) (x y : Space c)
    (h : JoinedIn (Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val) :
    AtLabel side c x ↔ AtLabel side c y := by
  have hp := joined_project side c x y h
  exact ⟨fun ⟨hg,hgPath⟩ => ⟨hg,hgPath.trans hp⟩, fun ⟨hg,hgPath⟩ => ⟨hg,hgPath.trans hp.symm⟩⟩

theorem bothLabels_iff (c : List Bool) (x y : Space c)
    (h : JoinedIn (Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val) :
    BothLabels c x ↔ BothLabels c y := forall_congr' (fun side => atLabel_iff side c x y h)

/-- The same accepted word meets the two prescribed components together. -/
theorem component_hit (c : List Bool) (x : Space c) (hx : BothLabels c x) :
    ∃ Gamma : List Bool, Gamma.length ≤ FormulaSignSlotRadialJointStratumSampler.tableBound c ∧
      ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid
          FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) w),
        w.length = SquareSampleCompleteVertices.width FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) ∧
        w.length ≤ FormulaSignSlotRadialJointStratumSampler.ownwordBound c ∧
        pair (pair c Gamma) w ∈ FormulaSignSlotRadialJointStratumSampler.language ∧
        ∃ a : Space c, BothLabels c a ∧
          HEq (SquareSampleCompleteVertices.candidate FormulaSignSlotRadialJointStratumSampler.input
            (pair c Gamma) w hw).val a.val := by
  obtain ⟨Gamma,hGamma,w,hw,hlen,hbound,hq,a,hpath,hpoint⟩ :=
    FormulaSignSlotRadialJointStratumSampler.component_hit c x
  exact ⟨Gamma,hGamma,w,hw,hlen,hbound,hq,a,(bothLabels_iff c x a hpath).mp hx,hpoint⟩

end LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
