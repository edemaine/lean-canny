/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderLabelClosedGeometry
/-! # Native external Replay identifies the same closed-source stratum projection -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderExternalLabelGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FormulaSignSlotRadialProviderLabelClosedGeometry FormulaSignSlotRadialProviderOriginalMarkedGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "field"=>FormulaSignSlotRadialProviderAtomic.field
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "n"=>CanonicalAuxiliaryCandidateCover.dimension
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input

private noncomputable def ExternalFields (c:List Bool) (values:ℕ→ℝ):Prop:=
  ∃ha:FormulaSignSlotRadialExternalReplay.accepted c,∀i<num c,
    FormulaSignSlotRadialExternalCoordinates.point c (FormulaSignSlotRadialExternalReplay.accepted_valid c ha) i=values i

theorem native_external_fields (c q:List Bool) (hv:A q) (hc:provider q=c)
    (hrole:FormulaSignSlotRadialExternalContext.external c) (hw:FormulaSignSlotRadialExternalCoordinates.OwnValid c):
    ∀i<num c,FormulaSignSlotRadialExternalCoordinates.point c hw i=field q hv i:=by
  have HRole:FormulaSignSlotRadialExternalContext.external (provider q):=by rwa [hc]
  have H0:ExternalFields (provider q) (field q hv):=
    FormulaSignSlotRadialProviderAtomic.ReplayFields.external_fields q hv HRole
  have H1:=Eq.mp (congrArg (fun ctx=>ExternalFields ctx (field q hv)) hc) H0
  obtain ⟨ha,HF⟩:=H1
  exact HF

private theorem homeomorph_forward_values (u:List Bool) (x:FormulaSignSlotCircularBoundedCover.Source u):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u) x).val=x.val:=rfl

private theorem homeomorph_project_coordinate (side:Bool) (c:List Bool)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (i:Fin (n (FormulaSignSlotRadialJointStratumLabels.source side c))):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph (FormulaSignSlotRadialJointStratumLabels.source side c))
      (FormulaSignSlotRadialJointStratumLabels.project side c x)).val i=
        FormulaSignSlotRadialProviderStratumProjection.projectedCoordinate side c x i:=
  congrFun (homeomorph_forward_values _ _) i

variable (H:List Bool) (k:ℕ) (Gamma label:List Bool) (side:Bool) (w:List Bool)
local notation "c"=>FormulaSignSlotRadialJointStratum.packet H k
local notation "u"=>FormulaSignSlotRadialJointLayout.source side H
local notation "ctx"=>FormulaSignSlotRadialExternalContext.packet H k Gamma label side w

theorem source_packet:FormulaSignSlotRadialJointStratumLabels.source side c=u:=by
  simp only [FormulaSignSlotRadialJointStratumLabels.source,
    FormulaSignSlotRadialProviderStratumProjection.header_packet]

noncomputable def projectAt (x:FormulaSignSlotRadialJointStratumLabels.Space c):
    FormulaSignSlotCircularBoundedCover.Source u:=source_packet H k side ▸ FormulaSignSlotRadialJointStratumLabels.project side c x

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  FormulaSignSlotRadialProviderAtomic.field FormulaSignSlotRadialExternalCoordinates.point

theorem projectAt_fields (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val):
    SourceFields u (projectAt H k side x)
      (FormulaSignSlotRadialExternalCoordinates.point ctx
        (FormulaSignSlotRadialProviderStratumProjection.own_valid H k Gamma label side w hw)):=by
  apply sourceFields_cast _ _ (source_packet H k side)
  intro i
  let j:Fin (FormulaSignSlotRadialJointLayout.circleCount side H):=
    Fin.cast (congrArg (FormulaSignSlotRadialJointLayout.circleCount side)
      (FormulaSignSlotRadialProviderStratumProjection.header_packet H k)) i
  have HE:=FormulaSignSlotRadialProviderStratumProjection.external_project_coordinate H k Gamma label side w hw x hx j
  have HI:Fin.cast (congrArg (FormulaSignSlotRadialJointLayout.circleCount side)
      (FormulaSignSlotRadialProviderStratumProjection.header_packet H k)).symm j=i:=Fin.ext rfl
  rw [HI] at HE
  rw [homeomorph_project_coordinate]
  exact HE.symm

theorem paired_providers (a ext:List Bool)
    (ha:provider a=FormulaSignSlotRadialProviderPair.oldOf ctx) (he:provider ext=ctx):
    provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext):=
  ha.trans (congrArg FormulaSignSlotRadialProviderPair.oldOf he.symm)

theorem original_old_provider (a:List Bool)
    (ha:provider a=FormulaSignSlotRadialProviderPair.oldOf ctx):
    FormulaSignSlotRadialProviderMarkedGeometry.original (provider a)=u:=
  (congrArg FormulaSignSlotRadialProviderMarkedGeometry.original ha).trans
    ((FormulaSignSlotRadialProviderPair.original_oldOf ctx).trans
      (FormulaSignSlotRadialExternalContext.original_packet H k Gamma label side w))

theorem external_closed_eq_project (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val)
    (a ext:List Bool) (he:A ext)
    (hpa:provider a=FormulaSignSlotRadialProviderPair.oldOf ctx) (hpe:provider ext=ctx):
    closedAtOriginal (provider a) u (original_old_provider H k Gamma label side w a hpa)
      (externalMarked a ext (paired_providers H k Gamma label side w a ext hpa hpe) he)=projectAt H k side x:=by
  have H0:SourceFields u
      (closedAtOriginal (provider a) u (original_old_provider H k Gamma label side w a hpa)
        (externalMarked a ext (paired_providers H k Gamma label side w a ext hpa hpe) he)) (field ext he):=by
    intro i
    exact external_closed_fields a ext (paired_providers H k Gamma label side w a ext hpa hpe) he u _ i
  have HP:=projectAt_fields H k Gamma label side w hw x hx
  have HV:=native_external_fields ctx ext he hpe
    (FormulaSignSlotRadialExternalContext.external_packet H k Gamma label side w)
    (FormulaSignSlotRadialProviderStratumProjection.own_valid H k Gamma label side w hw)
  have HN:num ctx=n u:=FormulaSignSlotRadialExternalContext.number_packet H k Gamma label side w
  have H1:SourceFields u (projectAt H k side x) (field ext he):=by
    intro i
    exact (HP i).trans (HV i.val (by rw [HN];exact i.isLt))
  exact sourceFields_ext u _ _ (field ext he) H0 H1

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderExternalLabelGeometry
