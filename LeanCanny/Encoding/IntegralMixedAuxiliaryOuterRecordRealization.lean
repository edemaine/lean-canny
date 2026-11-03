/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRealization
/-! # One correlated realization of the entire n+10 original prelude -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def integerCommands {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) :=
  IntegralMixedSourceIntegerPrelude.commands (parameters hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R)
    (source_cap hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R) (fun c=>number n c+10)
    (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R) root

theorem integerCommands_length {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) : (integerCommands hn ht ha R root).length=number n root+10 :=
  IntegralMixedSourceIntegerPrelude.commands_length _ _ _ _ _ _ _ _

theorem integer_suffix {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) :
    ((plan hn ht ha R).rules root).drop (IntegralMixedCausalRecordPlanBits.count root)=integerCommands hn ht ha R root :=
  by
    unfold plan IntegralMixedSourceIntegerRecordAppend.plan
    simpa only [IntegralMixedSourceIntegerRecordAppend.later_length,integerCommands,IntegralMixedSourceIntegerPrelude.plan] using
      (IntegralMixedSourceIntegerPrelude.extended_suffix (parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R) (spatial_cap hn ht ha)
        (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R) (fun c=>number n c+10)
        (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R)
        (IntegralMixedSourceIntegerRecordAppend.later (parameters hn ht ha)
          (fun c _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R c) (positive hn ht ha)
          (fun c _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R c) (spatial_cap hn ht ha) (fun c=>number n c+10))
        (fun c=>by rw [IntegralMixedSourceIntegerRecordAppend.later_length]; exact room hn ht ha c) root)

theorem integer_prefix {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) :
    paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (parameters hn ht ha) (plan hn ht ha R) root)
      ((plan hn ht ha R).rules root) (number n root+10)=integerCommands hn ht ha R root := by
  have HS:=integer_suffix hn ht ha R root
  have HD : (plan hn ht ha R).rules root=
      ((plan hn ht ha R).rules root).take (IntegralMixedCausalRecordPlanBits.count root)++integerCommands hn ht ha R root := by
    rw [←HS]
    exact (List.take_append_drop _ _).symm
  rw [IntegralMixedFramedHistoryScript.paddedPast_valid _ _ _ (by
    unfold plan IntegralMixedSourceIntegerRecordAppend.plan
    rw [IntegralMixedSourceIntegerPrelude.extended_length,IntegralMixedSourceIntegerRecordAppend.later_length]
    omega)]
  rw [IntegralMixedFramedHistoryScript.past,HD,List.reverse_append,List.take_append]
  have HL : (integerCommands hn ht ha R root).reverse.length=number n root+10 := by
    rw [List.length_reverse,integerCommands_length]
  rw [HL,Nat.sub_self,List.take_zero,List.append_nil]
  rw [←HL,List.take_length,List.reverse_reverse]

theorem realizes_prescribed {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) (x : ℕ→ℝ) (u v : ℝ)
    (hold : ∀i<number n root+8,((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
      (pair root (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
        (IntegralMixedAuxiliaryMarkedIntegerSource.values n t R root x u v i)=0) :
    IntegralMixedIntegerRealization.Realizes
      (run (IntegralMixedFramedHistoryFamilyBits.initial (parameters hn ht ha) (plan hn ht ha R) root)
        (integerCommands hn ht ha R root) (by
          rw [integerCommands_length]
          change number n root+10≤number n root+10+IntegralMixedCausalRecordPlanBits.count root+2+1+1
          omega))
      (fun i=>IntegralMixedAuxiliaryOuterIntegerSource.values n t R root x u v (number n root+10-1-i)) := by
  apply IntegralMixedSourceIntegerPrelude.realizes (parameters hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R)
    (source_cap hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R) (fun c=>number n c+10)
    (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R) root
    _ (fun i:Fin 0=>Fin.elim0 i) (fun i=>Fin.elim0 i) _
    (IntegralMixedAuxiliaryOuterIntegerSource.values n t R root x u v)
  exact IntegralMixedAuxiliaryOuterIntegerSource.roots hn ht ha R root x u v hold

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
