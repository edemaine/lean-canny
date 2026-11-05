/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicBeforeProbe
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicCompanions
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarked
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplay
/-! # Native source-aware atomic validity without an external old-label premise

One literal provider, checked record chain and complete own word satisfy
all historical cut/critical guards, latest captures, marked equations and
the actual OLD or source-associated EXTERNAL prelude replay.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def replayQuery (q : List Bool) := FormulaSignSlotRadialProviderReplay.packet (provider q) (context q) (word q)
theorem replayQuery_FP : replayQuery∈FP := mem_FP_pair provider_FP (mem_FP_pair context_FP word_FP)
theorem replay_provider (q : List Bool) : FormulaSignSlotRadialProviderReplay.context (replayQuery q)=provider q :=
  pairFst_pair _ _
noncomputable def Replay (q : List Bool) := replayQuery q∈
  FormulaSignSlotRadialProviderReplay.languageAt FormulaSignSlotRadialProviderRecordPlan.bank
theorem replay_decider : SpaceDecider {q | Replay q} :=
  (FormulaSignSlotRadialProviderReplay.deciderAt FormulaSignSlotRadialProviderRecordPlan.bank
    FormulaSignSlotRadialProviderRecordPlan.bank_access FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderRecordPlan.tables_native bank_represents).precompose replayQuery replayQuery_FP

noncomputable def Valid (q : List Bool) := CheckedGrammar q ∧ FullValid q ∧ BeforeProbe q ∧ CriticalScan q ∧
  companionQuery (dimension q) (initial q) q∈Companions.language ∧ Marked.Holds q ∧ Replay q
noncomputable def language : Language := {q | Valid q}

attribute [local irreducible] CheckedGrammar FullValid BeforeProbe CriticalScan Companions.language Marked.Holds Replay

theorem evaluator : SpaceFunction (fun q => [decide (Valid q)]) := by
  have EG := SpaceFunction.ofFP _ checkedGrammar_FP.flag_mem_FP
  have EV := full_decider.flagEvaluator
  have ET := beforeProbe_decider.flagEvaluator
  have EC := criticalScan_decider.flagEvaluator
  have EP := (Companions.decider.precompose
    (fun q => companionQuery (dimension q) (initial q) q) native_companionQuery).flagEvaluator
  have EM := Marked.decider.flagEvaluator
  have ER := replay_decider.flagEvaluator
  exact (EG.andFlags (EV.andFlags (ET.andFlags (EC.andFlags (EP.andFlags (EM.andFlags ER)))))).congr
    (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [Valid,Set.mem_ofPred_eq,Set.mem_preimage,
        List.cons.injEq,and_true,decide_eq_true_eq])
theorem decider : SpaceDecider language := by
  apply evaluator.decider (fun v => decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE

theorem valid_grammar (q : List Bool) (h : Valid q) : CheckedGrammar q := h.1
theorem valid_full (q : List Bool) (h : Valid q) : FullValid q := h.2.1
theorem valid_beforeProbe (q : List Bool) (h : Valid q) : BeforeProbe q := h.2.2.1
theorem valid_critical (q : List Bool) (h : Valid q) : CriticalScan q := h.2.2.2.1
theorem valid_companions (q : List Bool) (h : Valid q) :
    companionQuery (dimension q) (initial q) q∈Companions.language := h.2.2.2.2.1
theorem valid_marked (q : List Bool) (h : Valid q) : Marked.Holds q := h.2.2.2.2.2.1
theorem valid_replay (q : List Bool) (h : Valid q) : Replay q := h.2.2.2.2.2.2
theorem valid_word_bound (q : List Bool) (h : Valid q) :
    (word q).length≤providerWordBudget (provider q) := word_length_le q h.1 h.2.1
theorem valid_external_associated (q : List Bool) (h : Valid q)
    (he : FormulaSignSlotRadialExternalContext.external (provider q)) :
    FormulaSignSlotRadialProviderReplay.associated (provider q) := by
  have HR := valid_replay q h
  unfold Replay at HR
  have H := (FormulaSignSlotRadialProviderReplay.external_iff FormulaSignSlotRadialProviderRecordPlan.bank
    (replayQuery q) (by rw [replay_provider]; exact he)).mp HR
  simpa only [replay_provider] using H.1

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
