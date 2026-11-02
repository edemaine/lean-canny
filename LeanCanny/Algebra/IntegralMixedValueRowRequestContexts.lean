/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueRowContextFields
/-! # Every observed value-row request preserves the creating context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (answer : List Bool → List Bool)

theorem context21 : RequestsSatisfy (IntegralMixedFullRowBranch.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  have HC := IntegralMixedVirtualNativeLowerBits.fold_requests_bound (IntegralMixedFullRowNative.program P F) answer budget q c hc
  rcases (IntegralMixedFullRowRequest.requests_iff _ _ _ _ _ answer q c).mp HC with rfl | rfl
  · exact low_context P F q
  · exact scalar_context P F q

theorem context22 : RequestsSatisfy (IntegralMixedValueHomogeneousBranch.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := (IntegralMixedValueHomogeneousRequest.requests_iff P F answer budget q c).mp hc
  exact homogeneous_context P F q

theorem context23 : RequestsSatisfy (IntegralMixedValueReciprocalBranch.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := (IntegralMixedValueReciprocalRequest.requests_iff P F answer budget q c).mp hc
  exact reciprocal_context P F q

theorem context24 : RequestsSatisfy (IntegralMixedValueMacaulayBranch.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, rfl⟩ := (IntegralMixedValueMacaulayRequest.requests_iff P F answer budget q c).mp hc
  exact macaulay_context P F q

theorem context25 : RequestsSatisfy (IntegralMixedValueGramProductNative.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  rcases DependentTwoCall.requests_cases _ _ _ answer budget q c hc with hl | hr
  · rw [hl]; exact product_context P F true q
  · rw [hr]
    unfold IntegralMixedValueGramProductNative.right
    rw [pairFst_pair]
    exact product_context P F false q

theorem context26 : RequestsSatisfy (IntegralMixedValueGramSumNative.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  let C := IntegralMixedValueGramSumNative.program P F
  change C.controller.Requests answer budget q c at hc
  obtain ⟨t, _, _, _, he⟩ := hc
  rw [show C.controller.initial q = C.initial q from rfl, C.reference_iterate] at he
  rw [he]
  exact sum_context P q _

theorem requests_context : RequestsSatisfy (IntegralMixedValueRowDispatcher.machine P a F h) answer (ContextEq P) := by
  unfold IntegralMixedValueRowDispatcher.machine
  apply requestsSatisfy_choose _ _ answer _ (context21 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context22 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context23 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context24 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context25 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context26 P a F h answer)
  exact requestsSatisfy_zero answer _
end LeanCanny.Algebra.IntegralMixedValueRowContextBits
