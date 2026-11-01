/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationContextFields
/-! # Normalization scalar and streamed requests preserve context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] factorProgram IntegralMixedNormalizationTopBits.source IntegralMixedNormalizationTopBits.access momentEntryProgram

theorem two_context (P : Parameters) (left right post answer : List Bool → List Bool)
    (hl : ∀ q, ContextEq P q (left q)) (hr : ∀ z, get P .slot15 (right z) = get P .slot15 (pairFst z))
    (budget : List Bool → ℕ) (q c : List Bool)
    (hc : (DependentTwoCall.controller left right post).Requests answer budget q c) : ContextEq P q c := by
  rcases DependentTwoCall.requests_cases left right post answer budget q c hc with he | he
  · rw [he]; exact hl q
  · rw [he]; exact (hr _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

variable (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
  (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool)

theorem context0 : RequestsSatisfy (stage0 P a F hd) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := ((rawProgram P F).requests_iff answer budget q c).mp hc
  exact raw_context P F q

theorem context2 : RequestsSatisfy (stage2 P a F) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := ((entryProgram P).requests_iff answer budget q c).mp hc
  exact next_context P .originalCoefficient q

theorem context5 : RequestsSatisfy (stage5 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := ((factorProgram P F).requests_iff answer budget q c).mp hc
  exact factor_context P F q

theorem context7 : RequestsSatisfy (stage7 P a F height hb) answer (ContextEq P) := by
  intro q _ budget c hc
  change (zeroProgram P height).controller.Requests answer budget q c at hc
  obtain ⟨i, _, rfl⟩ := IntegerZeroBits.RecursiveStage.requests_cases (rootBudget P height) (smallTask P) answer budget q c hc
  exact (small_context P _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

theorem context8 : RequestsSatisfy (stage8 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨i, _, rfl⟩ := LowestCoefficientBits.RecursiveStage.requests_cases (matrixDimension P F) (zeroTask P) answer budget q c hc
  exact (zero_context P _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

theorem context9 : RequestsSatisfy (stage9 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  exact two_context P (indexTask P F) (inverseTask P) (inversePost P) answer (index_context P F) (inverse_context P) budget q c hc

theorem context10 : RequestsSatisfy (stage10 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  exact two_context P (termLeft P) (termRight P) (multiplyPost P) answer (next_context P .frozenPowerTerm)
    (fun z => next_context P .derivativeCoefficient (pairFst z)) budget q c hc

theorem context11 : RequestsSatisfy (stage11 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  let C := inverseSumProgram P F
  change C.controller.Requests answer budget q c at hc
  obtain ⟨t, _, _, _, he⟩ := hc
  rw [show C.controller.initial q = C.initial q from rfl, C.reference_iterate] at he
  rw [he]
  exact (term_context P _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

theorem context12 : RequestsSatisfy (stage12 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  exact two_context P (productLeft P) (productRight P) (multiplyPost P) answer
    (product_left_context P) (product_right_context P) budget q c hc

theorem context13 : RequestsSatisfy (stage13 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  let C := productSumProgram P F
  change C.controller.Requests answer budget q c at hc
  obtain ⟨t, _, _, _, he⟩ := hc
  rw [show C.controller.initial q = C.initial q from rfl, C.reference_iterate] at he
  rw [he]
  exact (product_loop_context P _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

theorem leading_stage_context : RequestsSatisfy (leadingStage P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  exact two_context P (indexTask P F) (leadingTask P) leadingPost answer (index_context P F) (leading_context P) budget q c hc

theorem lower_stage_context : RequestsSatisfy (lowerCoefficientStage P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := ((lowerCoefficientProgram P).requests_iff answer budget q c).mp hc
  exact next_context P .coordinateGradientProduct q

theorem context14 : RequestsSatisfy (stage14 P a F h hd) answer (ContextEq P) := by
  unfold stage14
  apply requestsSatisfy_choose
  · apply requestsSatisfy_withGuard _ _ _ answer _ (leading_stage_context P a F h answer)
    intro q hq
    exact (selected_iff P .eulerSum q).mpr ((selected14Matrix_iff P F q).mp ((top14_iff P F q).mp hq).1).1
  · apply requestsSatisfy_choose
    · apply requestsSatisfy_withGuard _ _ _ answer _ (lower_stage_context P a F h answer)
      intro q hq
      exact ((low14_iff P F q).mp hq).1
    · exact requestsSatisfy_zero answer _
end LeanCanny.Algebra.IntegralMixedNormalizationContextBits
