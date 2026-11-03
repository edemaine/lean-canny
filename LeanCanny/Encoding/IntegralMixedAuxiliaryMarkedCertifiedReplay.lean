/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateVertex
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerBankObservation
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerBank
public import LeanCanny.Algebra.IntegralMixedFramedFullObservation

/-! # The native certified bank observes the literal correlated replay -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCertifiedReplay
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedAuxiliaryMarkedIntegerPlan (parameters plan data certifiedParameters certifiedPlan certifiedData bankKey)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (replayState)
open IntegralMixedFramedHistoryFamilyBits (family keyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def sampleContext (ctx : List Bool) := pair ctx []

theorem rules_length {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) : ((plan hn ht ha R).rules ctx).length=number n ctx+8 := by
  unfold IntegralMixedAuxiliaryMarkedIntegerPlan.plan IntegralMixedSourceIntegerPrelude.plan
  rw [IntegralMixedSourceIntegerPrelude.commands_length]

theorem rules_cap {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) :
    ((plan hn ht ha R).rules ctx).length≤(parameters hn ht ha).cap ctx+1 := by
  rw [rules_length]
  change _+8≤_+8+2+1
  omega

theorem saved_key {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (ctx : List Bool) :
    bankKey n (sampleContext ctx)=keyAt ctx ((plan hn ht ha R).rules ctx).length [] := by
  simp only [bankKey,sampleContext,pairFst_pair,rules_length]

private theorem rows_key_congr (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool) (he : u=v) :
    HEq ((family P D H).state u).sampler.scalarPrefix.rows ((family P D H).state v).sampler.scalarPrefix.rows := by
  cases he
  rfl

attribute [local irreducible] parameters data

theorem rows_at_key {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx : List Bool) :
    HEq ((family (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).state
      (bankKey n (sampleContext ctx))).sampler.scalarPrefix.rows (replayState hn ht ha R ctx).sampler.scalarPrefix.rows := by
  have HC:=rules_cap hn ht ha R ctx
  exact (IntegralMixedAuxiliaryMarkedIntegerPlan.certified_rows hn ht ha hR _).trans
    ((rows_key_congr (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) _ _ (saved_key hn ht ha R ctx)).trans
      (IntegralMixedFramedFullObservation.rows (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) ctx [] HC
        (HC.trans (Nat.le_succ _))))

theorem data_at_key {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx : List Bool) :
    IntegralMixedFramedBankObservation.ofState
      ((family (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).state
        (bankKey n (sampleContext ctx)))=IntegralMixedFramedBankObservation.ofState (replayState hn ht ha R ctx) := by
  have HC:=rules_cap hn ht ha R ctx
  have HK:=congrArg (fun k=>IntegralMixedFramedBankObservation.ofState
    ((family (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)).state k)) (saved_key hn ht ha R ctx)
  exact (IntegralMixedAuxiliaryMarkedIntegerPlan.certified_bank hn ht ha hR _).trans
    (HK.trans (IntegralMixedFramedFullObservation.data (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
      ctx [] HC (HC.trans (Nat.le_succ _))))

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCertifiedReplay
