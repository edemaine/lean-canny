/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderOriginalMarkedGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderOldLabelGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumProjection
/-! # Literal closed-source points of actual provider marked projections -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderLabelClosedGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open FormulaSignSlotRadialProviderOriginalMarkedGeometry FormulaSignSlotRadialProviderPreludePhaseGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n"=>CanonicalAuxiliaryCandidateCover.dimension
local notation "t"=>CanonicalAuxiliaryCandidateCover.equation
local notation "hn"=>CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht"=>CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha"=>CanonicalAuxiliaryCandidateCover.equation_scope
local notation "Eqn"=>FormulaSignSlotRadialProviderMarkedGeometry.equation
local notation "Allow"=>FormulaSignSlotRadialProviderMarkedGeometry.allowance
local notation "Radius"=>FormulaSignSlotRadialProviderMarkedGeometry.radius
local notation "original"=>FormulaSignSlotRadialProviderMarkedGeometry.original
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "Mark" c=>BoundedRegularSource.Marked (Eqn c) (Allow c) (Allow c) (Radius c)

private theorem coordinate_heq {d e:ℕ} (hde:d=e) (p:Fin d→ℝ) (q:Fin e→ℝ)
    (he:HEq p q) (i:Fin d) (j:Fin e) (hi:i.val=j.val):p i=q j:=by
  cases hde
  cases eq_of_heq he
  exact congrArg p (Fin.ext hi)

noncomputable def closedAtOriginal (c u:List Bool) (hu:original c=u) (z:Mark c):
    FormulaSignSlotCircularBoundedCover.Source u:=hu ▸ markedClosedPoint c z

theorem closedAt_forward_heq (c u:List Bool) (hu:original c=u) (z:Mark c):
    HEq ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u) (closedAtOriginal c u hu z)).val
      (BoundedRegularSource.markedProjection _ _ _ _ z).val:=by
  subst u
  exact heq_of_eq (markedClosedPoint_forward_values c z)

theorem closedAt_joined_iff (c u:List Bool) (hu:original c=u) (z v:Mark c):
    JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c) z.val.val v.val.val ↔
      JoinedIn Set.univ (closedAtOriginal c u hu z) (closedAtOriginal c u hu v):=by
  subst u
  exact marked_closed_joined_iff c z v

theorem closedAt_marked_fields (c u:List Bool) (hu:original c=u) (q:List Bool) (hv:A q)
    (hc:provider q=c) (i:Fin (n u)):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u)
      (closedAtOriginal c u hu (markedAt c q hv hc))).val i=FormulaSignSlotRadialProviderAtomic.field q hv i.val:=by
  subst u
  exact (congrFun (markedClosedPoint_forward_values c (markedAt c q hv hc)) i).trans
    (markedAt_projection c q hv hc i)

noncomputable def sourceSample (u label:List Bool) (hg:AuxiliaryCandidateComponentCover.Good hn ht ha u label):
    FormulaSignSlotCircularBoundedCover.Source u:=
  (CanonicalAuxiliaryCandidateCover.sourceHomeomorph u).symm
    ⟨IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label (Classical.choose hg),
      (AuxiliaryCandidateComponentCover.evaluation _ _ _).trans (Classical.choose_spec hg)⟩

theorem sourceSample_forward (u label:List Bool) (hg:AuxiliaryCandidateComponentCover.Good hn ht ha u label):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u) (sourceSample u label hg)).val=
      IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label (Classical.choose hg):=by
  unfold sourceSample
  rw [Homeomorph.apply_symm_apply]

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  LeanCanny.ETR.Term.finitePolynomial FormulaSignSlotRadialProviderAtomic.field markedAt externalMarked
  IntegralMixedAuxiliaryCandidate.pointAt

theorem old_closed_eq_sample (u label aux q:List Bool) (hv:A q)
    (hc:provider q=FormulaSignSlotRadialOldProviderRealization.context u label aux)
    (hg:AuxiliaryCandidateComponentCover.Good hn ht ha u label):
    closedAtOriginal (FormulaSignSlotRadialOldProviderRealization.context u label aux) u
      (FormulaSignSlotRadialOldProviderRealization.original_context u label aux)
      (markedAt _ q hv hc)=sourceSample u label hg:=by
  obtain ⟨hp,HF⟩:=FormulaSignSlotRadialProviderOldLabelGeometry.pointAt_fields u label aux q hv hc
  apply (CanonicalAuxiliaryCandidateCover.sourceHomeomorph u).injective
  apply Subtype.ext
  funext i
  rw [closedAt_marked_fields,sourceSample_forward]
  exact (HF i).symm

theorem external_closed_fields (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext)
    (u:List Bool) (hu:original (provider a)=u) (i:Fin (n u)):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u)
      (closedAtOriginal (provider a) u hu (externalMarked a ext hp he))).val i=
        FormulaSignSlotRadialProviderAtomic.field ext he i.val:=by
  have HE:=(closedAt_forward_heq (provider a) u hu (externalMarked a ext hp he)).trans
    (externalMarked_projection_heq a ext hp he)
  have HN0:num (provider a)=n u:=congrArg n hu
  have HN:n u=num (provider ext):=HN0.symm.trans (FormulaSignSlotRadialProviderPairGeometry.number_pair a ext hp)
  let j:Fin (num (provider ext)):=Fin.cast HN i
  have HV:=coordinate_heq HN _ _ HE i j rfl
  exact HV.trans (by simpa only [j,Fin.val_cast] using markedAt_projection (provider ext) ext he rfl j)

noncomputable def SourceFields (u:List Bool) (p:FormulaSignSlotCircularBoundedCover.Source u) (values:ℕ→ℝ):Prop:=
  ∀i:Fin (n u),((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u) p).val i=values i.val

theorem sourceFields_cast (u v:List Bool) (hu:u=v) (p:FormulaSignSlotCircularBoundedCover.Source u)
    (values:ℕ→ℝ) (H:SourceFields u p values):SourceFields v (hu ▸ p) values:=by cases hu;exact H

theorem sourceFields_ext (u:List Bool) (p q:FormulaSignSlotCircularBoundedCover.Source u) (values:ℕ→ℝ)
    (HP:SourceFields u p values) (HQ:SourceFields u q values):p=q:=by
  apply (CanonicalAuxiliaryCandidateCover.sourceHomeomorph u).injective
  exact Subtype.ext (funext fun i=>(HP i).trans (HQ i).symm)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderLabelClosedGeometry
