/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordSpace
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackPlanned
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace
/-! # Honest arbitrary-caller-modulus controls for the actual record script

The base script is planned first. Attaching the modulus projects original
code through pairFst and preserves every literal source, record and birth.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularPlannedSnapshot
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

theorem planned (P : Parameters) (D : Plan P) (R : BoundedFullWriter.Readers)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R) (L F C : List Bool→ℕ) :
    BoundedRegularFramedOriginalBits.Snapshot (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) R := ⟨s.ambient,s.source⟩
end LeanCanny.Algebra.BoundedRegularPlannedSnapshot

namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem certifiedAccess {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : Access (certifiedParameters hn ht ha hR) :=
  IntegralMixedFramedNormalizationBits.planned_access (parameters hn ht ha) (access hn ht ha) (BinaryFn.const 3)
    (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)

theorem certifiedInputs {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedStepHeight.FamilyInputs (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) :=
  IntegralMixedFramedNormalizationBits.planned_familyInputs _ _ _ _ _ (familyInputs hn ht ha hR)

theorem certifiedSnapshot {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    BoundedRegularFramedOriginalBits.Snapshot (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) :=
  BoundedRegularPlannedSnapshot.planned (parameters hn ht ha) (plan hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) (snapshot hn ht ha R)
    (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)

noncomputable def callerData {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedRootPullback.data (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
    (certifiedData hn ht ha hR) pairFst IntegralMixedFramedModulusPacket.extra

noncomputable def callerControls {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Controls (lifted (certifiedParameters hn ht ha hR))
      (liftedPlan (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)) (callerData hn ht ha hR) :=
  IntegralMixedSourceIntegerRecordPullback.plannedCallerControls (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (source_cap hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) (fun _=>le_rfl)
    pairFst IntegralMixedFramedModulusPacket.extra (access hn ht ha)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR) pairFst_mem_FP IntegralMixedFramedModulusPacket.extra_binary
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders_native hn ht hR)
    (scope ha R) (snapshot hn ht ha R) (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (BinaryFn.const 3) (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)

theorem callerBounds {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (lifted (certifiedParameters hn ht ha hR))
      (liftedPlan (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)) (callerData hn ht ha hR) (callerControls hn ht ha hR) :=
  IntegralMixedSourceIntegerRecordPullback.plannedCallerBounds (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+8) (source_cap hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) (room hn ht ha) (fun _=>le_rfl)
    pairFst IntegralMixedFramedModulusPacket.extra (access hn ht ha)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR) pairFst_mem_FP IntegralMixedFramedModulusPacket.extra_binary
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R) (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders_native hn ht hR)
    (scope ha R) (snapshot hn ht ha R) (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (BinaryFn.const 3) (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)
    (familyInputs hn ht ha hR) (factor_positive hn ht ha) (fun _=>by decide)

theorem companion_evaluator {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR))) :=
  IntegralMixedFramedCurrentQCompanionBits.evaluator (certifiedParameters hn ht ha hR) (certifiedAccess hn ht ha hR)
    (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (callerData hn ht ha hR)
    (callerControls hn ht ha hR) (callerBounds hn ht ha hR)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
