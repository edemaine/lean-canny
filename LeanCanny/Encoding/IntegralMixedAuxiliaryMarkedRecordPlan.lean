/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerHeight
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordBounds
/-! # The original marked roots followed by a literal causal record table

The source remains the static bounded regular source. The table occupies the
first field of the outer context; original radius data stays outside integer
coefficient words. Width and horizon depend on syntax and record count only.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number degreeBound)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def parameters {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :=
  IntegralMixedSourceIntegerPrelude.parameters (fun c=>number n c+3) (IntegralMixedAuxiliaryMarkedIntegerPlan.degree t)
    (degreeBound hn ht ha) (fun c=>number n c+8+IntegralMixedCausalRecordPlanBits.count c)

theorem access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) : Access (parameters hn ht ha) :=
  IntegralMixedSourceIntegerPrelude.access ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 3))
    (IntegralMixedAuxiliaryMarkedIntegerPlan.degree_binary ht) (IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound_binary hn ht ha)
    (((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8)).add IntegralMixedCausalRecordPlanBits.count_unary)

theorem positive {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (root : List Bool) :
    0<(parameters hn ht ha).ambient root := by change 0<number n root+3; omega

theorem spatial_cap {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((parameters hn ht ha).ambient root+1) ((parameters hn ht ha).degree root)≤
      2^(parameters hn ht ha).width root := IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _ root

theorem source_cap {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) :
    PurePowerReductionBounds.dimension ((parameters hn ht ha).ambient root+1)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root).degree≤2^(parameters hn ht ha).width root := by
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
  exact (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension ((parameters hn ht ha).ambient root+1) ((parameters hn ht ha).degree root)≤
      IntegralMixedExceptionalBounds.auxiliaryCap ((parameters hn ht ha).ambient root+1) ((parameters hn ht ha).degree root)).trans
    (spatial_cap hn ht ha root)

theorem room {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (root : List Bool) :
    IntegralMixedCausalRecordPlanBits.count root+(number n root+8)+2≤(parameters hn ht ha).cap root+1 := by
  change _≤number n root+8+IntegralMixedCausalRecordPlanBits.count root+2+1
  omega

noncomputable def plan {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) :=
  IntegralMixedSourceIntegerRecordAppend.plan (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha)

noncomputable def data {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) :=
  IntegralMixedSourceIntegerRecordAppend.data (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (source_cap hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) (fun _=>le_rfl)

theorem integerOriginal {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedIntegerFamilyBits.Original (parameters hn ht ha)
      (IntegralMixedFramedIntegerBits.polynomial (parameters hn ht ha) (plan hn ht ha R)) :=
  IntegralMixedSourceIntegerRecordAppend.integerOriginal (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) (access hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
