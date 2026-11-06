/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderExternalLabelGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumSeeds
/-! # Literal stratum labels are witnessed by genuine native anchored seed pairs -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumLabelGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FormulaSignSlotRadialProviderGraph FormulaSignSlotRadialProviderPreludePhaseGeometry
open FormulaSignSlotRadialProviderOriginalMarkedGeometry FormulaSignSlotRadialProviderLabelClosedGeometry
open FormulaSignSlotRadialProviderExternalLabelGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n"=>CanonicalAuxiliaryCandidateCover.dimension
local notation "hn"=>CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht"=>CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha"=>CanonicalAuxiliaryCandidateCover.equation_scope
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "Geo"=>FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
local notation "original"=>FormulaSignSlotRadialProviderMarkedGeometry.original
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input

noncomputable def LabelAt (u label:List Bool) (p:FormulaSignSlotCircularBoundedCover.Source u):Prop:=
  ∃hg:AuxiliaryCandidateComponentCover.Good hn ht ha u label,JoinedIn Set.univ (sourceSample u label hg) p

private theorem labelAt_cast (u v:List Bool) (he:u=v) (label:List Bool)
    (p:FormulaSignSlotCircularBoundedCover.Source u):LabelAt u label p ↔LabelAt v label (he ▸ p):=by
  cases he
  rfl

private theorem labelAt_good_iff (u label:List Bool) (hg:AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (p:FormulaSignSlotCircularBoundedCover.Source u):LabelAt u label p ↔JoinedIn Set.univ (sourceSample u label hg) p:=by
  constructor
  · rintro ⟨_,H⟩
    exact H
  · intro H
    exact ⟨hg,H⟩

private theorem atLabel_def (side:Bool) (c:List Bool) (x:FormulaSignSlotRadialJointStratumLabels.Space c):
    FormulaSignSlotRadialJointStratumLabels.AtLabel side c x ↔
      LabelAt (FormulaSignSlotRadialJointStratumLabels.source side c)
        (FormulaSignSlotRadialJointStratumLabels.label side c) (FormulaSignSlotRadialJointStratumLabels.project side c x):=Iff.rfl

private theorem native_old_closed_eq_sample (u label aux a:List Bool) (hv:A a)
    (hc:provider a=FormulaSignSlotRadialOldProviderRealization.context u label aux)
    (ho:original (provider a)=u) (hg:AuxiliaryCandidateComponentCover.Good hn ht ha u label):
    closedAtOriginal (provider a) u ho (markedAt (provider a) a hv rfl)=sourceSample u label hg:=by
  obtain ⟨hp,HF⟩:=FormulaSignSlotRadialProviderOldLabelGeometry.pointAt_fields u label aux a hv hc
  apply (CanonicalAuxiliaryCandidateCover.sourceHomeomorph u).injective
  apply Subtype.ext
  funext i
  rw [closedAt_marked_fields,sourceSample_forward]
  exact (HF i).symm

private theorem attachment_at_provider (c q:List Bool) (hv:A q) (hc:provider q=c)
    (HJ:JoinedIn (Geo c) (pointAt c q hv hc) (preludeAt c q hv hc)):
    JoinedIn (Geo (provider q)) (pointAt (provider q) q hv rfl) (preludeAt (provider q) q hv rfl):=by
  subst c
  exact HJ

variable (H:List Bool) (k:ℕ) (Gamma:List Bool) (side:Bool) (w:List Bool)
local notation "c"=>FormulaSignSlotRadialJointStratum.packet H k
local notation "u"=>FormulaSignSlotRadialJointLayout.source side H
local notation "label"=>FormulaSignSlotRadialJointStratumLabels.label side c
local notation "ctx"=>FormulaSignSlotRadialExternalContext.packet H k Gamma label side w
local notation "oldctx"=>FormulaSignSlotRadialProviderPair.oldOf ctx
local notation "aux"=>pair (pair c Gamma) (pair [side] w)

theorem atLabel_packet_iff (x:FormulaSignSlotRadialJointStratumLabels.Space c):
    FormulaSignSlotRadialJointStratumLabels.AtLabel side c x ↔LabelAt u label (projectAt H k side x):=
  (atLabel_def side c x).trans (labelAt_cast _ _ (source_packet H k side) label _)

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  FormulaSignSlotRadialProviderAtomic.field markedAt externalMarked FormulaSignSlotRadialProviderAnchoredGeometry.externalPrelude

theorem atLabel_iff_joined_preludes (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val)
    (a ext:List Bool) (hv:A a) (he:A ext) (hpa:provider a=oldctx) (hpe:provider ext=ctx):
    FormulaSignSlotRadialJointStratumLabels.AtLabel side c x ↔
      JoinedIn (Geo (provider a)) (preludeAt (provider a) a hv rfl)
        (FormulaSignSlotRadialProviderAnchoredGeometry.externalPrelude a ext
          (paired_providers H k Gamma label side w a ext hpa hpe) he):=by
  have HOld:provider a=FormulaSignSlotRadialOldProviderRealization.context u label aux:=
    hpa.trans (FormulaSignSlotRadialProviderPair.oldOf_packet H k Gamma label side w)
  have HG:=FormulaSignSlotRadialProviderOldLabelGeometry.good_of_valid u label aux a hv HOld
  have HO:=original_old_provider H k Gamma label side w a hpa
  have HOldPoint:=native_old_closed_eq_sample u label aux a hv HOld HO HG
  have HExtPoint:=external_closed_eq_project H k Gamma label side w hw x hx a ext he hpa hpe
  have HM:=closedAt_joined_iff (provider a) u HO (markedAt (provider a) a hv rfl)
    (externalMarked a ext (paired_providers H k Gamma label side w a ext hpa hpe) he)
  rw [markedAt_values,externalMarked_values,HOldPoint,HExtPoint] at HM
  exact (atLabel_packet_iff H k side x).trans ((labelAt_good_iff u label HG _).trans HM.symm)

/-- Literal membership in the prescribed source component is equivalent to a
pair of honest freshly constructible native anchored seed words at these contexts. -/
theorem atLabel_iff_exists_anchored_pair (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (hq:pair (pair c Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val):
    FormulaSignSlotRadialJointStratumLabels.AtLabel side c x ↔
      ∃a ext,∃_hv:A a,∃_he:A ext,provider a=oldctx ∧provider ext=ctx ∧
        FormulaSignSlotRadialProviderAtomic.depth a=0 ∧FormulaSignSlotRadialProviderAtomic.depth ext=0 ∧
        pair a ext∈FormulaSignSlotRadialProviderAnchoredAssociation.language:=by
  constructor
  · intro HA
    obtain ⟨HG,_⟩:=(atLabel_packet_iff H k side x).mp HA
    obtain ⟨a,ext,hv,he,hpa,hpe,hda,hde,HOldPath,HExtPath⟩:=
      FormulaSignSlotRadialProviderStratumSeeds.exists_attached_pair H k Gamma label side w HG hw hq
    have HP:=paired_providers H k Gamma label side w a ext hpa hpe
    have HX:FormulaSignSlotRadialExternalContext.external (provider ext):=by
      rw [hpe]
      exact FormulaSignSlotRadialExternalContext.external_packet H k Gamma label side w
    have HJ:=(atLabel_iff_joined_preludes H k Gamma side w hw x hx a ext hv he hpa hpe).mp HA
    have HL:=FormulaSignSlotRadialProviderAnchoredGeometry.language_of_joined_preludes a ext hv he hda hde HP HX
      (attachment_at_provider oldctx a hv hpa HOldPath) (attachment_at_provider ctx ext he hpe HExtPath) HJ
    exact ⟨a,ext,hv,he,hpa,hpe,hda,hde,HL⟩
  · rintro ⟨a,ext,hv,he,hpa,hpe,hda,hde,HL⟩
    have HP:=paired_providers H k Gamma label side w a ext hpa hpe
    have HX:FormulaSignSlotRadialExternalContext.external (provider ext):=by
      rw [hpe]
      exact FormulaSignSlotRadialExternalContext.external_packet H k Gamma label side w
    have HJ:=FormulaSignSlotRadialProviderAnchoredGeometry.language_joined_preludes a ext hv he hda hde HP HX HL
    exact (atLabel_iff_joined_preludes H k Gamma side w hw x hx a ext hv he hpa hpe).mpr HJ

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumLabelGeometry
