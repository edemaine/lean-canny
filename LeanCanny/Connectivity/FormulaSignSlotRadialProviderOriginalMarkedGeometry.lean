/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredGeometry
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
/-! # Paired marked preludes have their literal original closed-source components -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderOriginalMarkedGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open FormulaSignSlotRadialProviderGraph FormulaSignSlotRadialProviderPreludePhaseGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n"=>CanonicalAuxiliaryCandidateCover.dimension
local notation "t"=>CanonicalAuxiliaryCandidateCover.equation
local notation "Orig"=>AuxiliaryCandidateRegularLift.original n t
local notation "Allow"=>AuxiliaryCandidateRegularLift.allowance t
local notation "Eqn"=>FormulaSignSlotRadialProviderMarkedGeometry.equation
local notation "Radius"=>FormulaSignSlotRadialProviderMarkedGeometry.radius
local notation "original"=>FormulaSignSlotRadialProviderMarkedGeometry.original
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid

noncomputable def OriginalMarked (z:List Bool×ℕ):Type:=
  BoundedRegularSource.Marked (Orig z.1) (Allow z.1) (Allow z.1) z.2

private theorem model_values (c d:List Bool×ℕ) (he:c=d) (z:OriginalMarked c):
    HEq ((cast (congrArg OriginalMarked he) z).val.val) z.val.val:=by cases he;rfl

private theorem model_projection (c d:List Bool×ℕ) (he:c=d) (z:OriginalMarked c):
    HEq (BoundedRegularSource.markedProjection _ _ _ _ (cast (congrArg OriginalMarked he) z)).val
      (BoundedRegularSource.markedProjection _ _ _ _ z).val:=by cases he;rfl

theorem pair_parameters (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)):
    (original (provider ext),Radius (provider ext))=(original (provider a),Radius (provider a)):=by
  apply Prod.ext
  · exact ((congrArg original hp).trans (FormulaSignSlotRadialProviderPair.original_oldOf _)).symm
  · exact ((congrArg Radius hp).trans (FormulaSignSlotRadialProviderPair.radius_oldOf _)).symm

noncomputable def markedModel (c q:List Bool) (hv:A q) (hc:provider q=c):
    OriginalMarked (original c,Radius c):=markedAt c q hv hc
private theorem markedModel_values (c q:List Bool) (hv:A q) (hc:provider q=c):
    (markedModel c q hv hc).val.val=(markedAt c q hv hc).val.val:=rfl
private theorem markedModel_projection (c q:List Bool) (hv:A q) (hc:provider q=c):
    (BoundedRegularSource.markedProjection _ _ _ _ (markedModel c q hv hc)).val=
      (BoundedRegularSource.markedProjection _ _ _ _ (markedAt c q hv hc)).val:=rfl

noncomputable def externalMarked (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext):
    OriginalMarked (original (provider a),Radius (provider a)):=
  cast (congrArg OriginalMarked (pair_parameters a ext hp)) (markedModel (provider ext) ext he rfl)

theorem equation_eq (c:List Bool):Eqn c=Orig (original c):=rfl
private theorem sourceHomeomorph_values (u:List Bool)
    (z:AuxiliaryCandidateComponentCover.Space n t u):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u).symm z).val=z.val:=rfl
theorem original_zero_term (u:List Bool) (p:Fin (n u)→ℝ)
    (hp:(Orig u).eval₂ (Int.castRingHom ℝ) p=0):(t u).eval (Formula.extend p)=0:=
  (Term.eval_finitePolynomial _ _ _).symm.trans hp

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation Term.finitePolynomial
  FormulaSignSlotRadialProviderMarkedGeometry.equation FormulaSignSlotRadialProviderMarkedGeometry.allowance
  FormulaSignSlotRadialProviderAtomic.field markedAt

theorem externalMarked_values_heq (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext):
    HEq (externalMarked a ext hp he).val.val (markedAt (provider ext) ext he rfl).val.val:=
  (model_values _ _ (pair_parameters a ext hp) _).trans (heq_of_eq (markedModel_values _ _ _ _))

theorem externalMarked_values (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext):
    (externalMarked a ext hp he).val.val=FormulaSignSlotRadialProviderAnchoredGeometry.externalPrelude a ext hp he:=
  eq_of_heq ((externalMarked_values_heq a ext hp he).trans
    ((heq_of_eq (markedAt_values (provider ext) ext he rfl)).trans
      (FormulaSignSlotRadialProviderAnchoredGeometry.externalPrelude_heq a ext hp he).symm))

theorem externalMarked_projection_heq (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext):
    HEq (BoundedRegularSource.markedProjection _ _ _ _ (externalMarked a ext hp he)).val
      (BoundedRegularSource.markedProjection _ _ _ _ (markedAt (provider ext) ext he rfl)).val:=
  (model_projection _ _ (pair_parameters a ext hp) _).trans (heq_of_eq (markedModel_projection _ _ _ _))

private theorem component_joined_iff {m:ℕ} (Q:MvPolynomial (Fin m) ℤ) (x y:Fin m→ℝ)
    (hx:Q.eval₂ (Int.castRingHom ℝ) x=0) :
    y∈connectedComponentIn (BoundedZeroSource.Original Q) x ↔JoinedIn (BoundedZeroSource.Original Q) x y:=by
  constructor
  · intro hy
    simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map,BoundedZeroSource.Original] using
      PolynomialComponentPaths.joinedIn_of_component (Q.map (Int.castRingHom ℝ)) x
        (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map,Set.mem_ofPred_eq] using hx) y
        (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map,BoundedZeroSource.Original] using hy)
  · intro H
    rw [connectedComponentIn_eq_image H.source_mem]
    exact ⟨⟨y,H.target_mem⟩,pathComponent_subset_component _ H.joined_subtype,rfl⟩

noncomputable def markedClosedPoint (c:List Bool)
    (z:BoundedRegularSource.Marked (Eqn c) (FormulaSignSlotRadialProviderMarkedGeometry.allowance c)
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance c) (Radius c)):
    FormulaSignSlotCircularBoundedCover.Source (original c):=
  (CanonicalAuxiliaryCandidateCover.sourceHomeomorph (original c)).symm
    ⟨(BoundedRegularSource.markedProjection _ _ _ _ z).val,by
      change (AuxiliaryTiltedTerm.polynomial (n (original c)) (t (original c))).eval _=0
      rw [AuxiliaryCandidateComponentCover.evaluation]
      apply original_zero_term
      have HZ:=(BoundedRegularSource.markedProjection _ _ _ _ z).property.1
      simpa only [equation_eq] using HZ⟩

theorem markedClosedPoint_forward_values (c:List Bool)
    (z:BoundedRegularSource.Marked (Eqn c) (FormulaSignSlotRadialProviderMarkedGeometry.allowance c)
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance c) (Radius c)):
    ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph (original c)) (markedClosedPoint c z)).val=
      (BoundedRegularSource.markedProjection _ _ _ _ z).val:=by
  unfold markedClosedPoint
  rw [Homeomorph.apply_symm_apply]


theorem source_original_joined_iff (u:List Bool) (x y:FormulaSignSlotCircularBoundedCover.Source u):
    JoinedIn Set.univ x y ↔JoinedIn (BoundedZeroSource.Original (Orig u))
      ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u) x).val
      ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph u) y).val:=by
  let e:=CanonicalAuxiliaryCandidateCover.sourceHomeomorph u
  have HSet:AuxiliaryCandidateComponentCover.Space n t u=BoundedZeroSource.Original (Orig u):=by
    ext v
    change (AuxiliaryTiltedTerm.polynomial (n u) (t u)).eval v=0 ↔
      ((t u).finitePolynomial (n u)).eval₂ (Int.castRingHom ℝ) v=0
    rw [AuxiliaryTiltedTerm.polynomial_eq_map,MvPolynomial.eval_map]
  constructor
  · intro H
    have HJ:Joined (e x) (e y):=(joinedIn_univ.mp H).map e.continuous
    have HR:JoinedIn (AuxiliaryCandidateComponentCover.Space n t u) (e x).val (e y).val:=
      (joinedIn_iff_joined (e x).property (e y).property).mpr HJ
    simpa only [HSet,e] using HR
  · intro H
    have HR:JoinedIn (AuxiliaryCandidateComponentCover.Space n t u) (e x).val (e y).val:=by
      simpa only [HSet,e] using H
    have HJ:Joined (e x) (e y):=(joinedIn_iff_joined (e x).property (e y).property).mp HR
    apply joinedIn_univ.mpr
    simpa only [Homeomorph.symm_apply_apply] using HJ.map e.symm.continuous


theorem marked_closed_joined_iff (c:List Bool)
    (z v:BoundedRegularSource.Marked (Eqn c) (FormulaSignSlotRadialProviderMarkedGeometry.allowance c)
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance c) (Radius c)):
    JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c) z.val.val v.val.val ↔
      JoinedIn Set.univ (markedClosedPoint c z) (markedClosedPoint c v):=by
  have HM:=FormulaSignSlotRadialProviderMarkedGeometry.marked_original_component_iff c z v
  have HJ:=component_joined_iff (Eqn c)
    (BoundedRegularSource.markedProjection _ _ _ _ z).val
    (BoundedRegularSource.markedProjection _ _ _ _ v).val
    (BoundedRegularSource.markedProjection _ _ _ _ z).property.1
  have HS:=source_original_joined_iff (original c) (markedClosedPoint c z) (markedClosedPoint c v)
  exact (HM.trans HJ).trans (by simpa only [equation_eq,markedClosedPoint_forward_values] using HS.symm)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderOriginalMarkedGeometry
