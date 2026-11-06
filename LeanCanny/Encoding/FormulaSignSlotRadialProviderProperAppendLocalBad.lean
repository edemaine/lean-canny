/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendFrozenValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadComplete
public import LeanCanny.Geometry.IntegralMixedChronologicalBadTransport
/-! # Genuine canonical bad-free intervals close the actual native NoBad guard -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "CTX" => FormulaSignSlotRadialProviderRecordPrefix.context

private theorem bad_snapshot_ambient (r : List Bool) :
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot r).ambient=(P).ambient r := rfl
private theorem bad_snapshot_source (r : List Bool) :
    HEq (FormulaSignSlotRadialProviderBadProbeParent.snapshot r).source
      (FormulaSignSlotRadialProviderRecordPlan.spatial r) := HEq.rfl
private theorem bad_context (q : List Bool) : FormulaSignSlotRadialProviderAtomic.context q=
    CTX (FormulaSignSlotRadialProviderAtomic.root q) := rfl
private theorem bad_congr (r s w v l k : List Bool) (hr : r=s) (hw : w=v) (hl : l=k)
    (hL : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (CTX r) w)
    (hR : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (CTX s) v) :
    FormulaSignSlotRadialProviderBadProbeParent.bad r w l hL=
      FormulaSignSlotRadialProviderBadProbeParent.bad s v k hR := by
  subst s
  subst v
  subst k
  rfl

private theorem bad_rule_transport {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (hm : m≤S) (r s : IntegralMixedCriticalSweep.Rule n) (hr : r=s)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (c : IntegralMixedRelativeCuts.Choices x hm r φ) (d : IntegralMixedRelativeCuts.Choices x hm s φ) :
    IntegralMixedSelectedCriticalCuts.bad x hm r φ c=IntegralMixedSelectedCriticalCuts.bad x hm s φ d := by
  subst s
  exact IntegralMixedCurrentQCoordinateScaling.bad_choices_eq x hm r φ c d

variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd E he
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd E he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd E he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd E he
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd E he
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd E he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd E he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd E he
local notation "h" => next d hk
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd E he
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "snp" => FormulaSignSlotRadialProviderBadProbeParent.snapshot r
local notation "q" => packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec side
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderBadProbeParent.snapshot FormulaSignSlotRadialProviderBadProbeParent.values
  FormulaSignSlotRadialProviderBadProbeParent.bad

private theorem canonical_data_rule :
    ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x))=
      cutRule x (d).frame h g hg := by
  rw [data_rule x d hk g g hg hg]
  have HG : (g).val=(d).labels.length+1 := rfl
  rw [HG,Nat.sub_self]
  rfl

private theorem bad_frozen_value (S : SampledLevel old hv hd left right R side pMID pChild)
    (i : Fin (d).labels.length) :
    FormulaSignSlotRadialProviderBadProbeParent.values r S.receipt.word S.receipt.valid
      ((snp).birth-1-((d).labels.get i).val)=V ((d).reference i) := by
  let label := ((d).labels.get i).val
  have HLabel : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen old) i.val)=label := by
    have HH := IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt
    rw [FormulaSignSlotRadialProviderRetainedAppend.parent_labels old hv hd E he] at HH
    exact HH
  have HP := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd E he
  have HLab : label<beginBirth old := ((d).labels.get i).isLt.trans_eq HP
  have HF := finish_le_full old hv hd left right R side
  have HE := finish_eq old hv hd left right R side
  have HM : midpointBirth old hv hd left right R=beginBirth old+R.result.commands.length := rfl
  have HBirth := FormulaSignSlotRadialProviderBadProbeParent.birth r
  have HFull : fullBirth old hv hd left right R side=FormulaSignSlotRadialProviderRecordPlan.count r+
      IntegralMixedCausalRecordPlanBits.count r := rfl
  have HFit : label<(snp).birth := by omega
  have HVal := FormulaSignSlotRadialProviderBadProbeParent.value_field r S.receipt.word S.receipt.valid
    ((snp).birth-1-label) (by omega)
  have HIndex : FormulaSignSlotRadialProviderRecordPlan.count r+
      (IntegralMixedCausalRecordPlanBits.count r-1)-1-((snp).birth-1-label)=label := by omega
  rw [HIndex] at HVal
  have HV := S.original_frozen_values i
  have HNative : FormulaSignSlotRadialProviderAtomic.bankField (CTX r) S.receipt.word S.receipt.valid label=
      V ((d).reference i) := by
    simpa only [FormulaSignSlotRadialProviderAtomic.field,context_packet,word_packet,HLabel] using HV
  exact HVal.trans HNative

private theorem bad_to_canonical (S : SampledLevel old hv hd left right R side pMID pChild)
    (v : ℝ) (hvBad : v∈FormulaSignSlotRadialProviderBadProbeParent.bad r S.receipt.word
      (FormulaSignSlotRadialProviderAtomic.frozen old) S.receipt.valid) :
    v∈IntegralMixedSelectedCriticalCuts.bad x hm (cutRule x (d).frame h g hg) phi choices := by
  have HP : FormulaSignSlotRadialProviderRecordPlan.providerContext c=
      FormulaSignSlotRadialProviderRecordPlan.providerContext r :=
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old E).trans
      (prepared_provider old R.leftSpec R.rightSpec side).symm
  have HD : (P).ambient c=(snp).ambient :=
    (FormulaSignSlotRadialProviderRecordPrefix.ambient c r HP).trans (bad_snapshot_ambient r).symm
  have HS : HEq (FormulaSignSlotRadialProviderRecordPlan.spatial c) (snp).source :=
    (FormulaSignSlotRadialProviderRecordPrefix.source_heq c r HP).trans (bad_snapshot_source r).symm
  have HC : IntegralMixedRelativeCuts.Choices x hm
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) phi := by
    rw [canonical_data_rule]
    exact choices
  have HBad : v∈(snp).bad (IntegralMixedChronologicalFrameCode.labels d)
      (FormulaSignSlotRadialProviderBadProbeParent.values r S.receipt.word S.receipt.valid) := by
    simpa only [FormulaSignSlotRadialProviderBadProbeParent.bad,
      FormulaSignSlotRadialProviderRetainedAppend.parent_labels] using hvBad
  have H := mem_bad_imp_of_reference_values_heq snp HD HS x hm d hk g hg rfl phi V
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he) HC
    (FormulaSignSlotRadialProviderBadProbeParent.values r S.receipt.word S.receipt.valid)
    (bad_frozen_value S) v HBad
  have HT := bad_rule_transport x hm _ _ canonical_data_rule phi HC choices
  exact (Iff.of_eq (congrArg (fun set : Set ℝ=>v∈set) HT)).mp H

theorem SampledLevel.no_bad (S : SampledLevel old hv hd left right R side pMID pChild)
    (hab : left.value V<right.value V)
    (havoid : ∀v,v∈Set.Ioo (left.value V) (right.value V)→
      v∉IntegralMixedSelectedCriticalCuts.bad x hm (cutRule x (d).frame h g hg) phi choices) :
    FormulaSignSlotRadialProviderProper.NoBad (q S.receipt.word) := by
  have HD : 0<FormulaSignSlotRadialProviderAtomic.depth (q S.receipt.word) := by rw [depth_packet];omega
  have HE := S.original_endpoint_fields
  apply (FormulaSignSlotRadialProviderProper.noBad_iff_original_bad_free _ S.atomic_valid HD
    (by rw [HE.1,HE.2];exact hab)).mpr
  intro v hvI hvBad
  have HI : v∈Set.Ioo (left.value V) (right.value V) := by
    change FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
      (IntegralMixedRoadmapProper.producer false (q S.receipt.word))<v ∧
      v<FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
        (IntegralMixedRoadmapProper.producer true (q S.receipt.word)) at hvI
    constructor
    · exact lt_of_eq_of_lt HE.1.symm hvI.1
    · exact lt_of_lt_of_eq hvI.2 HE.2
  have HB : v∈FormulaSignSlotRadialProviderBadProbeParent.bad r S.receipt.word
      (FormulaSignSlotRadialProviderAtomic.frozen old) S.receipt.valid := by
    have HBad := bad_congr _ _ _ _ _ _ (root_packet old R.leftSpec R.rightSpec side S.receipt.word)
      (word_packet _ _ _ _ _ _) (coarse_labels_packet old hv hd left right R side S.receipt.word)
      (FormulaSignSlotRadialProviderAtomic.full_valid _ S.atomic_valid) S.receipt.valid
    exact (Iff.of_eq (congrArg (fun set : Set ℝ=>v∈set) HBad)).mp hvBad
  exact havoid v HI (bad_to_canonical S v HB)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
