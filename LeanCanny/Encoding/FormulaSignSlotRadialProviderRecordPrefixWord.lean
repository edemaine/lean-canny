/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSample
/-! # Each actual provider word realizes every literal earlier prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "count" => FormulaSignSlotRadialProviderRecordPlan.count

def context (root : List Bool) := pair root []

theorem key_root (root : List Bool) : pairFst ((B).key (context root))=root := by
  change pairFst (keyAt (pairFst (pair root []))
    (FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst (pair root []))) [])=root
  simp only [pairFst_pair]

private theorem snapshot_birth (A : Parameters) (E : Plan A)
    (J : IntegralMixedFramedHistoryFamilyBits.Data A E) (key : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey A E J key).count=(family A E J).birth key := rfl

theorem full_prefix (root : List Bool) : prefixLength (B).parameters ((B).key (context root))=
    FormulaSignSlotRadialProviderRecordPlan.fullCount root := by
  have H := FormulaSignSlotRadialProviderRecordPlan.bank_count (context root)
  rw [snapshot_birth,family_birth] at H
  change prefixLength P (FormulaSignSlotRadialProviderRecordPlan.bankKey (context root))=_
  simpa only [context,pairFst_pair] using H

noncomputable def bankNatural (E : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input E) c w) : ℕ→ℝ :=
  IntegralFramedPhysicalPrefixObservation.tuple E.parameters E.plan E.data
    E.nodes E.factor E.seed E.bounds E.key E.positive c w hw

private theorem bankRoots (E : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input E) c w)
    (m : ℕ) (hm : m≤prefixLength E.parameters (E.key c)) :
    (IntegralFramedPhysicalPrefixObservation.atRoot E.parameters E.plan (pairFst (E.key c)) m
      (hm.trans (min_le_right _ _))).Roots (bankNatural E c w hw) :=
  IntegralFramedPhysicalPrefixObservation.roots E.parameters E.plan E.data
    E.nodes E.factor E.seed E.bounds E.key E.positive c w hw m hm

theorem bank_bound (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    count root+j≤(B).parameters.cap root+1 := bound root j hj

theorem bank_observation (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    IntegralFramedPhysicalPrefixObservation.atRoot (B).parameters (B).plan root (count root+j)
      (bank_bound root j hj)=observation root j hj := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank observation

noncomputable def natural (root w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context root) w) : ℕ→ℝ :=
  bankNatural B (context root) w hw

theorem word_roots (root w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context root) w)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    (observation root j hj).Roots (natural root w hw) := by
  have HM : count root+j≤prefixLength (B).parameters ((B).key (context root)) := by
    rw [full_prefix]
    change _≤count root+IntegralMixedCausalRecordPlanBits.count root
    omega
  have HR := bankRoots B (context root) w hw (count root+j) HM
  have HE := IntegralFramedPhysicalPrefixObservation.at_congr (B).parameters (B).plan
    (pairFst ((B).key (context root))) root (count root+j) (count root+j)
    (HM.trans (min_le_right _ _)) (bank_bound root j hj) (key_root root) rfl
  exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots (natural root w hw))
    (HE.trans (bank_observation root j hj))).mp HR

theorem transfer_word_roots (a b w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context a) w)
    (hp : FormulaSignSlotRadialProviderRecordPlan.providerContext a=
      FormulaSignSlotRadialProviderRecordPlan.providerContext b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    (observation b j (hj.trans_eq hc)).Roots (natural a w hw) := by
  rw [←observation_eq a b hp hc j hj hcode]
  exact word_roots a w hw j hj

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
