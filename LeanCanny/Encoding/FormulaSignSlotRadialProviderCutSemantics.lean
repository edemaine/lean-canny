/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutFactor
/-! # Actual provider cut guards are exactly own-prefix cut receipts -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutSemantics
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderRecordPrefix (context cutParent cutSaved ownCutReceipt)
open FormulaSignSlotRadialProviderCutReadback
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => family P D H
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalBankTerm.env
  FormulaSignSlotRadialProviderAtomic.Cuts.Guards FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
  ownCutReceipt quotient IntegralFramedCreatingCut.ParentCut IntegralFramedCreatingCut.IsCut
  IntegralMixedPrefixSnapshot.familyCutReceipt
  FormulaSignSlotRadialProviderRecordPrefix.observation

variable (r w : List Bool)
  (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w)
  (j : ℕ) (hj : j<IntegralMixedCausalRecordPlanBits.count r)
local notation "b" => N r+j
local notation "old" => cutSaved r b
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "factor" => IntegralMixedRelativeCuts.factor x (IntegralMixedCutSource.Family.birth_bound G old)
  (IntegralMixedCutSource.Family.rule G old) (IntegralMixedCutSource.Family.kind G old)

/-- All four native guards use the creating-prefix algebra and the same own word. -/
theorem guards_iff_ownReceipt
    (hc : FormulaSignSlotRadialProviderAtomic.Cuts.StageCut (stage r w b)) :
    FormulaSignSlotRadialProviderAtomic.Cuts.Guards (stage r w b) ↔ ownCutReceipt r w hw j hj := by
  unfold ownCutReceipt
  have HB : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    omega
  have HC : IntegralFramedCreatingCut.ParentCut P D (cutParent r b) := parent_cut r w b hc
  have HCmd : IntegralFramedCreatingCut.IsCut (instruction P D old).command := by
    unfold IntegralFramedCreatingCut.ParentCut at HC
    exact HC
  have HQ := quotient_field r w hw b HB
  constructor
  · intro hg
    obtain ⟨φ,hφ,hcg,hroot⟩ := (guards_iff_factor_receipt r w hw b HB HC).mp hg
    apply (IntegralMixedPrefixSnapshot.familyCutReceipt_iff P D H old _ _ HCmd).mpr
    refine ⟨φ,quotients_at r w hw j hj φ hφ,hcg,?_⟩
    exact (congrArg (fun a : ℝ=>(factor).eval₂ φ.toRingHom a) HQ).symm.trans hroot
  · intro hr
    obtain ⟨φ,hv,hcg,hroot⟩ := (IntegralMixedPrefixSnapshot.familyCutReceipt_iff P D H old _ _ HCmd).mp hr
    obtain ⟨ψ,hψ,_⟩ := coefficient_evaluation r w hw b HB
    have HValues := quotients_at r w hw j hj ψ hψ
    have HE : φ=ψ := IntegralMixedPrefixSnapshot.hom_eq_of_quotients x
      (family_canonical P D H old) φ ψ (fun i=>(hv i).trans (HValues i).symm)
    apply (guards_iff_factor_receipt r w hw b HB HC).mpr
    refine ⟨ψ,hψ,?_,?_⟩
    · simpa only [HE] using hcg
    · exact (congrArg (fun a : ℝ=>(factor).eval₂ ψ.toRingHom a) HQ).trans
        (by simpa only [HE] using hroot)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutSemantics
