/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordControls
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPlanned
/-! # Original-only native space for the marked prelude and causal records

All seven routines use the actual decoded records, with native original
LOW/leading/affine/scale leaves and charged current-Q slopes. Height and
modulus ceilings are derived; no stage or coefficient evaluator is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev certifiedParameters {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedNormalizationBits.planned (parameters hn ht ha) (fun _=>3) (factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
noncomputable abbrev certifiedPlan {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedNormalizationBits.plannedPlan (parameters hn ht ha) (plan hn ht ha R)
    (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
noncomputable abbrev certifiedData {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedNormalizationBits.plannedData (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)

theorem scope {n : List Bool→ℕ} {t : List Bool→Term}
    (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) (key : List Bool) :
    (TermView.term ((IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R).source key)).arity≤
      (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R).dim key := by
  simpa only [IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders,BoundedFullWriter.Readers.comp,
    BoundedRegularLowCoefficient.readers,Function.comp_apply,TermView.term_toBits,number] using ha (original (pairFst key))

noncomputable def certifiedControls {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Controls (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) :=
  IntegralMixedSourceIntegerRecordAppend.plannedControls (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (source_cap hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) (fun _=>le_rfl)
    (access hn ht ha) ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders_native hn ht hR)
    (scope ha R) (snapshot hn ht ha R) (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (BinaryFn.const 3) (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)

theorem certifiedBounds {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (certifiedControls hn ht ha hR) :=
  IntegralMixedSourceIntegerRecordAppend.plannedBounds (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (source_cap hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) (fun _=>le_rfl)
    (access hn ht ha) ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders_native hn ht hR)
    (scope ha R) (snapshot hn ht ha R) (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (BinaryFn.const 3) (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)
    (familyInputs hn ht ha hR) (factor_positive hn ht ha) (fun _=>by decide)

theorem model_space {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    SpaceFunction (IntegralMixedFramedCurrentQNativeBits.machine (certifiedParameters hn ht ha hR)
      (IntegralMixedFramedNormalizationBits.planned_access (parameters hn ht ha) (access hn ht ha) (BinaryFn.const 3)
        (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR))
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (certifiedControls hn ht ha hR)).model :=
  IntegralMixedFramedCurrentQNativeBits.model_space _ _ _ _ _ (certifiedBounds hn ht ha hR)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
