/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerOriginal
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerHeight
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQRootControls
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace
/-! # An original-only certified marked bank compatible with caller-root lifting

The base budgets are derived before the caller modulus is attached. Height and
modulus fields change; every source, command, scalar width and horizon stays
literal, and no equality of the two packed task encodings is asserted.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev certifiedParameters {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedNormalizationBits.planned (parameters hn ht ha) (fun _=>1) (fun _=>1) (seed hn ht ha hR)
noncomputable abbrev certifiedPlan {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedNormalizationBits.plannedPlan (parameters hn ht ha) (plan hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR)
noncomputable abbrev certifiedData {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedNormalizationBits.plannedData (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR)

theorem certifiedAccess {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) : Access (certifiedParameters hn ht ha hR) :=
  IntegralMixedFramedNormalizationBits.planned_access (parameters hn ht ha) (access hn ht ha)
    (BinaryFn.const 1) (BinaryFn.const 1) (seed_binary hn ht ha hR)

theorem certifiedInputs {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedStepHeight.FamilyInputs (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (fun _=>1) (fun _=>1) (seed hn ht ha hR) :=
  IntegralMixedFramedNormalizationBits.planned_familyInputs _ _ _ _ _ (familyInputs hn ht ha hR)

noncomputable def certifiedCallerData {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  IntegralMixedFramedRootPullback.data (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
    pairFst IntegralMixedFramedModulusPacket.extra

theorem certifiedRepresents {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedHeaderBits.Represents (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (certifiedData hn ht ha hR) (tables hn ht ha) :=
  BoundedRegularIntegerCurrentQBits.represents_planned (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (tables hn ht ha) (tables_represents hn ht ha R) (fun _=>1) (fun _=>1) (seed hn ht ha hR)

noncomputable def certifiedCallerControls {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  BoundedRegularIntegerCurrentQBits.pullbackControls (certifiedParameters hn ht ha hR) (certifiedAccess hn ht ha hR)
    (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) ((originalSyntax hn ht ha hR).planned (fun _=>1) (fun _=>1) (seed hn ht ha hR))
    (tables hn ht ha) (tables_native hn ht ha) (certifiedRepresents hn ht ha hR)
    pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra IntegralMixedFramedModulusPacket.extra_binary
    (fun _=>1) (fun _=>1) (seed hn ht ha hR) (BinaryFn.const 1) (BinaryFn.const 1) (seed_binary hn ht ha hR)

theorem certifiedCallerBounds {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (lifted (certifiedParameters hn ht ha hR))
      (liftedPlan (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)) (certifiedCallerData hn ht ha hR)
      (certifiedCallerControls hn ht ha hR) :=
  BoundedRegularIntegerCurrentQBits.pullbackBounds (certifiedParameters hn ht ha hR) (certifiedAccess hn ht ha hR)
    (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) ((originalSyntax hn ht ha hR).planned (fun _=>1) (fun _=>1) (seed hn ht ha hR))
    (tables hn ht ha) (tables_native hn ht ha) (certifiedRepresents hn ht ha hR)
    pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra IntegralMixedFramedModulusPacket.extra_binary
    (fun _=>1) (fun _=>1) (seed hn ht ha hR) (BinaryFn.const 1) (BinaryFn.const 1) (seed_binary hn ht ha hR)
    (certifiedInputs hn ht ha hR) (fun _=>le_rfl) (fun _=>le_rfl)
    (IntegralMixedFramedNormalizationBits.planned_budget (parameters hn ht ha) (fun _=>1) (fun _=>1) (seed hn ht ha hR))

theorem certified_state {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (certifiedData hn ht ha hR)).state key)
      ((IntegralMixedFramedHistoryFamilyBits.family (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)).state key) :=
  BoundedRegularIntegerCurrentQBits.state_planned (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _=>1) (fun _=>1) (seed hn ht ha hR) key

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
