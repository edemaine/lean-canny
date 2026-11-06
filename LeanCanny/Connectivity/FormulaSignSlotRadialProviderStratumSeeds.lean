/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumProjection
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderPair
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstSeedConstruct
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludeTargetGeometry
/-! # Genuine OLD and EXTERNAL component seeds retain their own attachment paths -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumSeeds
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FormulaSignSlotRadialProviderGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "Geo"=>FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input

private theorem attached_of_readback (c q:List Bool) (hv:A q) (hc:provider q=c)
    (z p:Fin (num c+4)→ℝ) (hp:HEq (FormulaSignSlotRadialProviderAtomic.point q hv) p)
    (hf:∀i:Fin (num c+4),FormulaSignSlotRadialProviderAtomic.field q hv i.val=z i)
    (HJ:JoinedIn (Geo c) z p):JoinedIn (Geo c) (pointAt c q hv hc) (preludeAt c q hv hc):=by
  have HP:pointAt c q hv hc=p:=eq_of_heq ((native_pointAt_heq c q hv hc).symm.trans hp)
  have HF:preludeAt c q hv hc=z:=funext hf
  rw [HP,HF]
  exact HJ.symm

private theorem attached_context (c d q:List Bool) (he:c=d) (hv:A q) (hc:provider q=c)
    (HJ:JoinedIn (Geo c) (pointAt c q hv hc) (preludeAt c q hv hc)):
    ∃hd:provider q=d,JoinedIn (Geo d) (pointAt d q hv hd) (preludeAt d q hv hd):=by
  cases he
  exact ⟨hc,HJ⟩

variable (H:List Bool) (k:ℕ) (Gamma label:List Bool) (side:Bool) (w:List Bool)
local notation "u"=>FormulaSignSlotRadialJointLayout.source side H
local notation "aux"=>pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) (pair [side] w)
local notation "extctx"=>FormulaSignSlotRadialExternalContext.packet H k Gamma label side w
local notation "oldctx"=>FormulaSignSlotRadialProviderPair.oldOf extctx

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.field pointAt preludeAt

/-- Both words are freshly sampled from genuine component-critical points.
The two attachment paths are outputs, not hypotheses about arbitrary valid words. -/
theorem exists_attached_pair
    (hg:AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope u label)
    (hw:SquareSampleCompleteVertices.Valid F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq:pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language):
    ∃a ext,∃ha:A a,∃he:A ext,∃hpa:provider a=oldctx,∃hpe:provider ext=extctx,
      FormulaSignSlotRadialProviderAtomic.depth a=0 ∧FormulaSignSlotRadialProviderAtomic.depth ext=0 ∧
      JoinedIn (Geo oldctx) (pointAt oldctx a ha hpa) (preludeAt oldctx a ha hpa) ∧
      JoinedIn (Geo extctx) (pointAt extctx ext he hpe) (preludeAt extctx ext he hpe):=by
  let cOld:=FormulaSignSlotRadialOldProviderRealization.context u label aux
  obtain ⟨a,wA,hA,pA,hPointA,hPathA,hFieldsA,_⟩:=FormulaSignSlotRadialProviderFirstSeed.exists_old_seed u label aux hg
  let qa:=FormulaSignSlotRadialProviderFirstSeed.packet cOld wA
  have HPA:provider qa=cOld:=FormulaSignSlotRadialProviderFirstSeed.provider_packet cOld wA
  have HJA:=attached_of_readback cOld qa hA HPA _ pA hPointA hFieldsA hPathA
  have HOld:cOld=oldctx:=(FormulaSignSlotRadialProviderPair.oldOf_packet H k Gamma label side w).symm
  obtain ⟨hpa,HOldPath⟩:=attached_context cOld oldctx qa HOld hA HPA HJA
  have HWO:=FormulaSignSlotRadialProviderStratumProjection.own_valid H k Gamma label side w hw
  obtain ⟨b,wE,hE,pE,hPointE,hPathE,hFieldsE,_⟩:=
    FormulaSignSlotRadialProviderFirstSeed.exists_external_seed H k Gamma label side w HWO hq
  let qe:=FormulaSignSlotRadialProviderFirstSeed.packet extctx wE
  have HPE:provider qe=extctx:=FormulaSignSlotRadialProviderFirstSeed.provider_packet extctx wE
  have HJE:=attached_of_readback extctx qe hE HPE _ pE hPointE hFieldsE hPathE
  exact ⟨qa,qe,hA,hE,hpa,HPE,FormulaSignSlotRadialProviderFirstSeed.depth_packet cOld wA,
    FormulaSignSlotRadialProviderFirstSeed.depth_packet extctx wE,HOldPath,HJE⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumSeeds
