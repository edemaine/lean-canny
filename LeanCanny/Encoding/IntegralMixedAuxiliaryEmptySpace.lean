/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyFamilyInputs
public import LeanCanny.Encoding.IntegralMixedEmptyTiltedNative
/-! # The complete empty auxiliary arithmetic model has original-only space cost

The input dimension, original term syntax and semantic arity scope construct
all task parameters, source descriptions, command headers, original scalar
cells, chronological height bounds, and automatic height/modulus planning.
No script bound or coefficient/matrix evaluator is a supplied premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def machine {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :=
  IntegralMixedEmptyTiltedNative.plannedMachine (parameters n t) (access hn ht) (description hn ht ha)
    (ambient_positive n t) (auxiliary_cap n t) (room n t) (source_width n t)

theorem model_space {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    SpaceFunction (machine hn ht ha).model :=
  IntegralMixedEmptyTiltedNative.planned_model_space (parameters n t) (access hn ht) (description hn ht ha)
    (ambient_positive n t) (auxiliary_cap n t) (room n t) (source_width n t) (familyInputs hn ht ha)
end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
