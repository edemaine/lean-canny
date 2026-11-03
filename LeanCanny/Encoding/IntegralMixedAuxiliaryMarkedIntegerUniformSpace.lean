/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerOriginal
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerHeight
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQPlanned
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionPlannedSpace
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackBounds
/-! # Original-only marked-prelude companion entries at every caller modulus

The caller modulus augments the root, then the native budgets are planned.
Every original source and saved birth is pulled back through the full root.
No integer term serialization or interpreted matrix/evaluator input occurs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def liftedData {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool → ℕ) :=
  IntegralMixedFramedRootPullback.data (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    pairFst IntegralMixedFramedModulusPacket.extra

noncomputable def uniformControls {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  BoundedRegularIntegerCurrentQBits.plannedControls (lifted (parameters hn ht ha))
    (lifted_access (parameters hn ht ha) (access hn ht ha))
    (liftedPlan (parameters hn ht ha) (plan hn ht ha R)) (liftedData hn ht ha R)
    ((originalSyntax hn ht ha hR).pullback pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra)
    (IntegralMixedFramedRootPullback.tables (tables hn ht ha) pairFst)
    (IntegralMixedFramedRootPullback.tablesAccess (tables hn ht ha) (tables_native hn ht ha) pairFst pairFst_mem_FP)
    (IntegralMixedFramedRootPullback.represents (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
      (tables hn ht ha) (tables_represents hn ht ha R) pairFst IntegralMixedFramedModulusPacket.extra)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR ∘ pairFst)
    (BinaryFn.const 1) (BinaryFn.const 1) ((seed_binary hn ht ha hR).comp pairFst_mem_FP)

theorem uniformBounds {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Bounds
      (IntegralMixedFramedCurrentQCompanionPlannedBits.parameters (parameters hn ht ha) (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst))
      (IntegralMixedFramedCurrentQCompanionPlannedBits.plan (parameters hn ht ha) (plan hn ht ha R) (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst))
      (IntegralMixedFramedCurrentQCompanionPlannedBits.data (parameters hn ht ha) (plan hn ht ha R) (liftedData hn ht ha R)
        (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst)) (uniformControls hn ht ha hR) :=
  BoundedRegularIntegerCurrentQBits.plannedBounds _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (IntegralMixedFramedRootPullback.familyInputs (parameters hn ht ha) (plan hn ht ha R) pairFst IntegralMixedFramedModulusPacket.extra
      (fun _=>1) (fun _=>1) (seed hn ht ha hR) (familyInputs hn ht ha hR)) (fun _=>le_rfl) (fun _=>le_rfl)

theorem companion_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    SpaceFunction (PaddedIntegralGeneratorSource.value
      (IntegralMixedFramedCompanionBits.source (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R))) :=
  IntegralMixedFramedCurrentQCompanionPlannedBits.evaluator (parameters hn ht ha) (access hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (liftedData hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR∘pairFst) (BinaryFn.const 1) (BinaryFn.const 1)
    ((seed_binary hn ht ha hR).comp pairFst_mem_FP) (uniformControls hn ht ha hR) (uniformBounds hn ht ha hR)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
