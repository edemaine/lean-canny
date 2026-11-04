/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedJointFieldReadback
/-! # The same sampled joint tuple is the verifier's full natural tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedJointNatural
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def BankJoint (K :IntegralFramedBankQuery.Bank) (c w :List Bool) (u :ℕ→ℝ):Prop:=
  ∀hv :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w,
    ∀i :Fin (IntegralFramedPhysicalSquare.count K.parameters K.plan (K.key c)),
      IntegralFramedPhysicalSquare.joint K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
        K.key K.positive c w hv i=u i.val

private theorem bank_natural (K :IntegralFramedBankQuery.Bank) (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w)
    (u :ℕ→ℝ) (HJ :BankJoint K c w u)
    (i :Fin (IntegralFramedPhysicalSquare.count K.parameters K.plan (K.key c))):
    IntegralFramedPhysicalSquare.naturalPoint K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hw i.val=u i.val:=
  (IntegralFramedPhysicalSquare.naturalPoint_at K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
    K.key K.positive c w hw i).trans (HJ hw i)

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralMixedMarkedPrefixFieldReadback.natural

theorem natural_eq (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (pair root []) w) (u :ℕ→ℝ)
    (HJ :IntegralMixedMarkedJointFieldReadback.Joint hn ht ha hR0 root w hw u)
    (i :ℕ) (hi :i<(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).arity):
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw i=u i:=by
  have HE :B=BP:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
    rfl
  have HP :BankJoint BP (pair root []) w u:=by intro hv;exact HJ
  have HN :BankJoint B (pair root []) w u:=
    (congrArg (fun K=>BankJoint K (pair root []) w u) HE).mpr HP
  have HC :IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key (pair root []))=
      (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).arity:=
    congrArg IntegralMixedFramedRunObservation.Data.arity
      (IntegralMixedMarkedPrefixFieldReadback.terminal_bank_data hn ht ha hR0 root)
  unfold IntegralMixedMarkedPrefixFieldReadback.natural
  exact bank_natural B (pair root []) w hw u HN ⟨i,hi.trans_eq HC.symm⟩

end LeanCanny.Encoding.IntegralMixedMarkedJointNatural
