/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionOriginalSpace
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptySpace
/-! # Actual empty auxiliary companions from original input syntax alone

Original dimension and term syntax construct every source, prefix, original
leaf, modulus budget and native arithmetic controller. No companion, scalar,
degree, coefficient or matrix evaluator is an input premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters

noncomputable def companionSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    PaddedIntegralGeneratorSource.Source :=
  IntegralMixedFramedCompanionBits.source (parameters n t) (plan hn ht ha) (data hn ht ha)

theorem companion_value_space {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (companionSource hn ht ha)) := by
  apply IntegralMixedFramedCompanionUniformBits.original_evaluator (parameters n t) (access hn ht)
    (plan hn ht ha) (data hn ht ha)
    (IntegralMixedEmptyTiltedNative.inputSyntax (parameters n t) (access hn ht) (description hn ht ha)
      (ambient_positive n t) (auxiliary_cap n t) (room n t) (source_width n t))
    (familyInputs hn ht ha) (description hn ht ha).factor_positive
  exact fun _ => Nat.le_refl 1

theorem companion_arity_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    UnaryFn (companionSource hn ht ha).arity :=
  IntegralMixedFramedCompanionUniformBits.source_arity_unary (parameters n t) (access hn ht) _ _

theorem companion_width_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    UnaryFn (companionSource hn ht ha).width :=
  IntegralMixedFramedCompanionUniformBits.source_width_unary (parameters n t) (access hn ht) _ _

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
