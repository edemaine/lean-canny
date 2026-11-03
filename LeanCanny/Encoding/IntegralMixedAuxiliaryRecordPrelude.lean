/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordCaller
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordCaller
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPrefix
/-! # The marked and outer record plans retain the exact integer prelude

These are the actual record-plan horizon and width, including all serialized
later records. Budget planning changes neither. There is no identification
with the smaller static integer plan, and no later solvability premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNormalizationBits
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
noncomputable def plannedCommands (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ) (key : List Bool):=
  commands (planned P L F C) (plannedPlan P D L F C) key

theorem plannedCommands_eq (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ) (key : List Bool) :
    plannedCommands P D L F C key=commands P D key:=rfl
end LeanCanny.Algebra.IntegralMixedFramedNormalizationBits

namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  (R : List Bool→ℕ)

noncomputable def recordPrelude : Plan (parameters hn ht ha) :=
  IntegralMixedSourceIntegerRecordAppend.preludePlan (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha)

theorem record_prelude_commands (root tail : List Bool) :
    commands (parameters hn ht ha) (plan hn ht ha R) (keyAt root (number n root+8) tail)=
      (recordPrelude hn ht ha R).rules (pairFst (keyAt root (number n root+8) tail)) :=
  IntegralMixedSourceIntegerRecordAppend.prelude_commands_key (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) root tail

theorem record_prelude_initial (root : List Bool) :
    initial (parameters hn ht ha) (plan hn ht ha R) root=
      initial (parameters hn ht ha) (recordPrelude hn ht ha R) root:=rfl

noncomputable def certifiedRecordPrelude (hR : BinaryFn R) : Plan (certifiedParameters hn ht ha hR):=
  IntegralMixedFramedNormalizationBits.plannedPlan (parameters hn ht ha) (recordPrelude hn ht ha R)
    (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)

attribute [local irreducible] parameters plan recordPrelude factor

theorem certified_prelude_commands (hR : BinaryFn R) (root tail : List Bool) :
    commands (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (keyAt root (number n root+8) tail)=
      (certifiedRecordPrelude hn ht ha R hR).rules (pairFst (keyAt root (number n root+8) tail)) :=by
  exact (IntegralMixedFramedNormalizationBits.plannedCommands_eq (parameters hn ht ha) (plan hn ht ha R)
    (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) _).trans
    (record_prelude_commands hn ht ha R root tail)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan

namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  (R : List Bool→ℕ)

noncomputable def recordPrelude : Plan (parameters hn ht ha) :=
  IntegralMixedSourceIntegerRecordAppend.preludePlan (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+10) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R)
    (source_degree_cap hn ht ha R) (room hn ht ha)

theorem record_prelude_commands (root tail : List Bool) :
    commands (parameters hn ht ha) (plan hn ht ha R) (keyAt root (number n root+10) tail)=
      (recordPrelude hn ht ha R).rules (pairFst (keyAt root (number n root+10) tail)) :=
  IntegralMixedSourceIntegerRecordAppend.prelude_commands_key (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+10) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R)
    (source_degree_cap hn ht ha R) (room hn ht ha) root tail

theorem record_prelude_initial (root : List Bool) :
    initial (parameters hn ht ha) (plan hn ht ha R) root=
      initial (parameters hn ht ha) (recordPrelude hn ht ha R) root:=rfl

noncomputable def certifiedRecordPrelude (hR : BinaryFn R) : Plan (certifiedParameters hn ht ha hR):=
  IntegralMixedFramedNormalizationBits.plannedPlan (parameters hn ht ha) (recordPrelude hn ht ha R)
    (fun _=>3) (factor hn ht ha) (seed hn ht ha hR)

attribute [local irreducible] parameters plan recordPrelude factor

theorem certified_prelude_commands (hR : BinaryFn R) (root tail : List Bool) :
    commands (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (keyAt root (number n root+10) tail)=
      (certifiedRecordPrelude hn ht ha R hR).rules (pairFst (keyAt root (number n root+10) tail)) :=by
  exact (IntegralMixedFramedNormalizationBits.plannedCommands_eq (parameters hn ht ha) (plan hn ht ha R)
    (fun _=>3) (factor hn ht ha) (seed hn ht ha hR) _).trans
    (record_prelude_commands hn ht ha R root tail)

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
