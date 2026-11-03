/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordHeight
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerData
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordControls
/-! # All seven native routines from original marked-source and record syntax

The actual integer sources, regular LOW/leading leaves, affine midpoint rows,
scale masks and charged current-Q slopes are constructed here. No coefficient,
height, matrix, current-bank or stage evaluator is a hypothesis.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem instruction_source {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction (parameters hn ht ha) (plan hn ht ha R) key).source=
      IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R (pairFst key) :=
  IntegralMixedSourceIntegerRecordAppend.instruction_source (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+10) (source_cap hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R)
    (source_degree_cap hn ht ha R) (room hn ht ha) key

theorem snapshot {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) :
    BoundedRegularFramedOriginalBits.Snapshot (parameters hn ht ha) (plan hn ht ha R)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) where
  ambient _:=rfl
  source key:=by rw [instruction_source]; rfl

noncomputable def controls {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Controls (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) :=
  IntegralMixedSourceIntegerRecordAppend.currentQControls (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+10) (source_cap hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R)
    (source_degree_cap hn ht ha R) (room hn ht ha) (fun _=>le_rfl)
    (access hn ht ha) ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 10))
    (IntegralMixedAuxiliaryOuterIntegerSource.access hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders_native hn ht hR)
    (fun key=>by
      simpa only [IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders,BoundedFullWriter.Readers.comp,
        BoundedRegularLowCoefficient.readers,Function.comp_apply,TermView.term_toBits,number] using ha (original (pairFst key)))
    (snapshot hn ht ha R) (fun _=>3) (factor hn ht ha) (seed hn ht ha hR)
    (BinaryFn.const 3) (factor_binary hn ht ha) (seed_binary hn ht ha hR)

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
