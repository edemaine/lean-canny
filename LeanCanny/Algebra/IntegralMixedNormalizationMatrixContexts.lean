/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationSimpleContexts
/-! # Actual normalization matrix requests retain their creating context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedNormalizationTopBits IntegralBerkowitzBlockBits IntegralMixedNormalizationMomentTasks
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
  (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F)
  (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool)
  (hm : IntegralMixedNormalizationDispatcherBits.Matches P a F h hd height hb answer)

attribute [local irreducible] IntegralMixedNormalizationTopBits.source IntegralMixedNormalizationTopBits.access topPowerAccess topPowerFamily IntegralMixedNormalizationTopBits.momentAccess

include g hm in
theorem context1 : RequestsSatisfy (stage1 P a F h) answer (ContextEq P) := by
  intro q hs budget c hc
  have H := (selected_iff P .derivativeCoefficient q).mp hs
  have HR := topPower_replies P F g answer (IntegralMixedNormalizationDispatcherBits.top P a F h hd height hb answer hm) q H.1 H.2.1
  obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local (topPowerAccess P F)
    (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient) answer q HR budget c hc
  exact (matrix_context P .originalCoefficient _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

theorem context3 : RequestsSatisfy (stage3 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff
    (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (source P F))
    (rowTask P (source P F)) (columnTask P (source P F)) (matrixTask P (source P F)) answer budget q c).mp hc
  rcases MatrixMoment.EntryBits.routed_cases
    (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h))
    (rowTask P (source P F)) (columnTask P (source P F)) (matrixTask P (source P F))
    (IntegralCriticalFlatMomentEntryBits.input P (source P F) q) hg with hr | hk | hm
  · rw [hchild, hr]
    exact (routed_context P (source P F) (rowQuery (source P F)) (row_parent _) _).trans
      (congrArg (get P .slot15) (IntegralCriticalFlatMomentEntryBits.request_parent P (source P F) q _))
  · rw [hchild, hk]
    exact (routed_context P (source P F) (columnQuery (source P F)) (column_parent _) _).trans
      (congrArg (get P .slot15) (IntegralCriticalFlatMomentEntryBits.request_parent P (source P F) q _))
  · rw [hchild, hm]
    exact (routed_context P (source P F) (matrixQuery (source P F)) (matrix_parent _) _).trans
      (congrArg (get P .slot15) (IntegralCriticalFlatMomentEntryBits.request_parent P (source P F) q _))

include g hm in
theorem context4 : RequestsSatisfy (stage4 P a F h) answer (ContextEq P) := by
  intro q hs budget c hc
  have H := (selected_iff P .factorPower q).mp hs
  have HR := moment_replies P F g answer (IntegralMixedNormalizationDispatcherBits.moment P a F h hd height hb answer hm) q H.1 H.2.1
  obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
    (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
    (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q HR budget c hc
  exact (matrix_context P .monomialFactor _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

include g hm in
theorem context6 : RequestsSatisfy (stage6 P a F h) answer (ContextEq P) := by
  intro q hs budget c hc
  have H := (selected_iff P .productPower q).mp hs
  have HR := factor_replies P F g answer (IntegralMixedNormalizationDispatcherBits.factor P a F h hd height hb answer hm) q H.1 H.2.1
  obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
    (source P F) (access P a F h) (IntegralCriticalFlatMatrixQuery.writer P .productEntry) answer q HR budget c hc
  exact (matrix_context P .productEntry _).trans (congrArg (get P .slot15) (pairFst_pair _ _))
end LeanCanny.Algebra.IntegralMixedNormalizationContextBits
