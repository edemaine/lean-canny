/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCutSelection
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceBeforeProbe
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
/-! # Creating cut stages are literal raw-record commands -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceStages
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedFramedHistoryScript IntegralFramedCreatingCut
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem isCut_heq {a b B C : ℕ} (x : Instruction a B) (y : Instruction b C)
    (en : a = b) (eB : B = C) (hi : HEq x y) : IsCut x.command ↔ IsCut y.command := by
  cases en
  cases eB
  cases eq_of_heq hi
  rfl


private theorem producer_cap (P Q : IntegralCriticalHistoryTask.Parameters)
    (T : IntegralMixedHeaderTablesBits.Tables) (key : List Bool) (h : P.cap (pairFst key) = Q.cap (pairFst key)) :
    IntegralMixedHeaderTablesBits.producer P T key = IntegralMixedHeaderTablesBits.producer Q T key := by
  simp only [IntegralMixedHeaderTablesBits.producer, IntegralMixedFullHistoryFamilyBits.prefixLength, h]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem bank_cap {R : List Bool → ℕ} (hR : BinaryFn R) (root : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap root =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap root := rfl

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan

private theorem native_cut_iff {S m : ℕ} {I : Type} (ctx : List Bool) (R : List Bool → ℕ)
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R) S
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m I) (code : List Bool) :
    IsCut (CoefficientMarkedRecordNative.instruction hn ht ha ctx R x code).command ↔
      IntegralMixedUnitRecordCode.critical code = false := by
  unfold CoefficientMarkedRecordNative.instruction IntegralMixedCausalRecordBits.instantiate
    IntegralMixedCausalUnitRecordBits.record
  cases hc : IntegralMixedUnitRecordCode.critical code <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, IsCut, IntegralMixedCausalRecordBits.Template.command,
      Bool.true_eq_false]

theorem raw_cut_iff (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :
    IsCut (IntegralMixedFramedHistoryFamilyBits.instruction (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)).command ↔
      IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false := by
  have HI := CoefficientMarkedRecordRuleSelection.instruction_heq hn ht ha ctx R k hk aux
  have HN := congrArg (fun root => IntegralMixedAuxiliaryMarkedIntegerSource.number n root + 3)
    (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx k aux)
  have HB := congrArg (CoefficientMarkedIntegerBirth.width hn ht ha)
    (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx k aux)
  have HT := isCut_heq _ _ HN HB HI
  exact HT.trans (native_cut_iff hn ht ha ctx R
    (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le) _)

/-- Classification reads literal instruction headers, whose original cap and
entire table are radius-independent, even for non-cut and padded stages. -/
theorem command_context {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan key).command.context =
      (IntegralMixedHeaderTablesBits.producer (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) key).context := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  have hp := IntegralMixedFramedHeaderBits.producer_eq B.parameters B.plan B.data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) key
  have hh := (congrArg IntegralMixedCommandHeaderBits.Header.context hp).trans
    (IntegralMixedCommandHeaderBits.command_context _)
  have hc := producer_cap B.parameters (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) T key
    (bank_cap hn ht ha hR (pairFst key))
  have htable := CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR
  exact hh.symm.trans ((congrArg IntegralMixedCommandHeaderBits.Header.context hc).trans
    (congrArg (fun table => (IntegralMixedHeaderTablesBits.producer
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) table key).context) htable))

theorem cut_radius_iff {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S) (key : List Bool) :
    IsCut (IntegralMixedFramedHistoryFamilyBits.instruction (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan key).command ↔
    IsCut (IntegralMixedFramedHistoryFamilyBits.instruction (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hS false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hS false).plan key).command := by
  rw [isCut_iff_context, isCut_iff_context, command_context hn ht ha hR, command_context hn ht ha hS]

end LeanCanny.Encoding.CoefficientMarkedRecordTraceStages
