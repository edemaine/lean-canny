/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludePhaseGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
/-! # An actual OLD replay and marked prelude imply the literal candidate is Good -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderOldLabelGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open FormulaSignSlotRadialProviderPreludePhaseGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n"=>CanonicalAuxiliaryCandidateCover.dimension
local notation "t"=>CanonicalAuxiliaryCandidateCover.equation
local notation "hn"=>CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht"=>CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha"=>CanonicalAuxiliaryCandidateCover.equation_scope
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "field"=>FormulaSignSlotRadialProviderAtomic.field
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "original"=>FormulaSignSlotRadialProviderMarkedGeometry.original
local notation "Eqn"=>FormulaSignSlotRadialProviderMarkedGeometry.equation

private noncomputable def CandidateFields (L:List Bool) (v:ℕ→ℝ):Prop:=
  ∃hp:IntegralMixedAuxiliaryCandidate.Valid hn ht ha L,
    ∀i:Fin (n (pairFst L)),IntegralMixedAuxiliaryCandidate.point hn ht ha L hp i=v i.val

private theorem fields_pair (u label:List Bool) (v:ℕ→ℝ) (H:CandidateFields (pair u label) v):
    ∃hp:IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label),
      ∀i:Fin (n u),IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label hp i=v i.val:=by
  obtain ⟨hp,HF⟩:=H
  refine ⟨hp,fun i=>?_⟩
  have HI:i.val<n (pairFst (pair u label)):=by rw [pairFst_pair];exact i.isLt
  have HE:=congrFun (FormulaSignSlotRadialOldProviderRealization.pointAt_values hn ht ha u label hp).1 i.val
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left i.isLt] at HE
  exact HE.symm.trans (HF ⟨i.val,HI⟩)

attribute [local irreducible] IntegralMixedAuxiliaryCandidate.Valid IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.pointAt CanonicalAuxiliaryCandidateCover.equation Term.finitePolynomial
  FormulaSignSlotRadialProviderAtomic.field

private theorem actual_fields (c q:List Bool) (hv:A q) (hc:provider q=c)
    (hrole:¬FormulaSignSlotRadialExternalContext.external c):CandidateFields (pairFst c) (field q hv):=by
  have HRole:¬FormulaSignSlotRadialExternalContext.external (provider q):=by rwa [hc]
  have H0:CandidateFields (pairFst (provider q)) (field q hv):=
    FormulaSignSlotRadialProviderAtomic.ReplayFields.old_fields q hv HRole
  exact Eq.mp (congrArg (fun ctx=>CandidateFields (pairFst ctx) (field q hv)) hc) H0

private def ZeroFields (u:List Bool) (v:ℕ→ℝ):Prop:=
  (AuxiliaryCandidateRegularLift.original n t u).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=0

private theorem marked_zero_fields (c q:List Bool) (hv:A q) (hc:provider q=c):ZeroFields (original c) (field q hv):=by
  let z:=markedAt c q hv hc
  have HP:(BoundedRegularSource.markedProjection _ _ _ _ z).val=(fun i=>field q hv i.val):=
    funext (fun i=>markedAt_projection c q hv hc i)
  have HZ:=(BoundedRegularSource.markedProjection _ _ _ _ z).property.1
  have HV:(Eqn c).eval₂ (Int.castRingHom ℝ) (fun i=>field q hv i.val)=0:=
    (congrArg (fun p=>(Eqn c).eval₂ (Int.castRingHom ℝ) p) HP).symm.trans HZ
  simpa only [ZeroFields,FormulaSignSlotRadialProviderMarkedGeometry.equation] using HV

theorem pointAt_fields (u label aux q:List Bool) (hv:A q)
    (hc:provider q=FormulaSignSlotRadialOldProviderRealization.context u label aux):
    ∃hp:IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label),
      ∀i:Fin (n u),IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label hp i=field q hv i.val:=by
  let c:=FormulaSignSlotRadialOldProviderRealization.context u label aux
  have HF:=actual_fields c q hv hc (FormulaSignSlotRadialOldProviderRealization.old_context u label aux)
  have HP:pairFst c=pair u label:=pairFst_pair _ _
  exact fields_pair u label (field q hv) (Eq.mp (congrArg (fun L=>CandidateFields L (field q hv)) HP) HF)

theorem good_of_valid (u label aux q:List Bool) (hv:A q)
    (hc:provider q=FormulaSignSlotRadialOldProviderRealization.context u label aux):
    AuxiliaryCandidateComponentCover.Good hn ht ha u label:=by
  obtain ⟨hp,HP⟩:=pointAt_fields u label aux q hv hc
  have H0:=marked_zero_fields (FormulaSignSlotRadialOldProviderRealization.context u label aux) q hv hc
  have HZ:=Eq.mp (congrArg (fun source=>ZeroFields source (field q hv))
    (FormulaSignSlotRadialOldProviderRealization.original_context u label aux)) H0
  refine ⟨hp,?_⟩
  have HE:IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label hp=(fun i=>field q hv i.val):=funext HP
  rw [HE]
  exact (Term.eval_finitePolynomial _ _ _).symm.trans HZ

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderOldLabelGeometry
