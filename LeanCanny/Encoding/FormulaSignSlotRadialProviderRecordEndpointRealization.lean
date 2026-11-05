/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordInterpretation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerRealization
public import LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
/-! # External marked endpoints realize the actual full-record saved prelude -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordEndpointRealization
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR
open IntegralMixedFramedHistoryFamilyBits IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def savedPreludeState (root tail : List Bool) :=
  (IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
    FormulaSignSlotRadialProviderRecordPlan.certifiedPlan FormulaSignSlotRadialProviderRecordPlan.certifiedData).state
    (keyAt root (FormulaSignSlotRadialProviderRecordPlan.count root) tail)

attribute [local irreducible] Term.finitePolynomial CanonicalAuxiliaryCandidateCover.equation
  AuxiliaryCandidateRegularLift.original FormulaSignSlotRadialProviderIntegerSource.source
  FormulaSignSlotRadialProviderRecordPlan.parameters

variable (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w records aux tail : List Bool)
local notation "ctx" => FormulaSignSlotRadialExternalContext.packet H k Gamma label side w
local notation "root" => FormulaSignSlotRadialProviderRecordPlan.root ctx records aux
local notation "m" => CanonicalAuxiliaryCandidateCover.dimension (FormulaSignSlotRadialJointLayout.source side H)
local notation "q" => AuxiliaryCandidateRegularLift.original CanonicalAuxiliaryCandidateCover.dimension
  CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialJointLayout.source side H)
local notation "r" => FormulaSignSlotRadialExternalPrelude.radius ctx
local notation "E" => AuxiliaryCandidateRegularLift.allowance CanonicalAuxiliaryCandidateCover.equation
  (FormulaSignSlotRadialJointLayout.source side H)

theorem exists_external_saved_realization
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    ∃ a : BoundedZeroSource.Bounded q r, ∃ v : ℕ→ℝ,
      IntegralMixedIntegerRealization.Realizes (savedPreludeState root tail)
        (fun j=>v (FormulaSignSlotRadialProviderRecordPlan.count root-1-j)) ∧
      (fun i : Fin (m+4)=>v i.val)=(BoundedRegularSource.markedLift q E E r a).val.val ∧
      ∀i : Fin m,a.val i=FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val := by
  obtain ⟨a,v,hv,hm,ha⟩ := FormulaSignSlotRadialProviderIntegerRealization.exists_external_values
    H k Gamma label side w hw hq
  refine ⟨a,v,?_,hm,ha⟩
  apply FormulaSignSlotRadialProviderRecordPlan.certified_prelude_key_realizes
  intro i _
  simpa only [FormulaSignSlotRadialProviderRecordPlan.providerContext_root] using hv i

theorem old_saved_realization (u label metadata records aux tail : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope u label) :
    IntegralMixedIntegerRealization.Realizes
      (savedPreludeState (FormulaSignSlotRadialProviderRecordPlan.root
        (FormulaSignSlotRadialOldProviderRealization.context u label metadata) records aux) tail)
      (fun j=>FormulaSignSlotRadialOldProviderRealization.values u label metadata hg
        (FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderRecordPlan.root
          (FormulaSignSlotRadialOldProviderRealization.context u label metadata) records aux)-1-j)) := by
  apply FormulaSignSlotRadialProviderRecordPlan.certified_prelude_key_realizes
  intro i _
  simpa only [FormulaSignSlotRadialProviderRecordPlan.providerContext_root] using
    FormulaSignSlotRadialOldProviderRealization.roots u label metadata hg i

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordEndpointRealization
