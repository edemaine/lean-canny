/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperFrames
/-! # Current single-call upper replies identify the actual scalar models -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

theorem moment_route_birth (F : Scripts) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (p : List Bool) :
    birth F.toParameters (IntegralCriticalFlatMomentTasks.task F.toParameters (characteristic F) route p) =
      birth F.toParameters (original p) := by
  change birth F.toParameters (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
    (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F)
      (route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet F.toParameters) p)))) = _
  rw [IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatBerkowitzQuery.entry_parent,
    IntegralCriticalFlatMomentTasks.task_parent F.toParameters route hr]

theorem moment_route_phase (F : Scripts) (route : List Bool → List Bool) (p : List Bool) :
    isPhase .actionEntry (IntegralCriticalFlatMomentTasks.task F.toParameters (characteristic F) route p) := by
  change phase (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
    (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F)
      (route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet F.toParameters) p)))) = _
  exact IntegralCriticalFlatMatrixQuery.writer_phase _ _ _

theorem moment_requested (F : Scripts) (h : Controls F) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hp : isPhase .momentEntry q)
    (hc : (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).controller.Requests reply budget q c) :
    IntegralCriticalTotalCompanionBits.valid F c ∧ isPhase .actionEntry c := by
  have HB : birth F.toParameters c = birth F.toParameters q ∧ isPhase .actionEntry c := by
    have HT (route : List Bool → List Bool) (hr : ∀ p, original (route p) = original (original p)) (v : List Bool) :
        birth F.toParameters (IntegralCriticalFlatMomentTasks.task F.toParameters (characteristic F) route
          (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input F.toParameters (characteristic F) q)) v)) =
          birth F.toParameters q ∧ isPhase .actionEntry
            (IntegralCriticalFlatMomentTasks.task F.toParameters (characteristic F) route
              (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input F.toParameters (characteristic F) q)) v)) :=
      ⟨(moment_route_birth F route hr _).trans (congrArg (birth F.toParameters)
        (IntegralCriticalFlatMomentEntryBits.request_parent F.toParameters (characteristic F) q v)), moment_route_phase F route _⟩
    obtain ⟨hg, he⟩ := (MatrixMoment.EntryBits.program_requests_iff
      (IntegralCriticalFlatMomentEntryBits.bits F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h))
      (IntegralCriticalFlatMomentEntryBits.input F.toParameters (characteristic F))
      (IntegralCriticalFlatMomentTasks.rowTask F.toParameters (characteristic F))
      (IntegralCriticalFlatMomentTasks.columnTask F.toParameters (characteristic F))
      (IntegralCriticalFlatMomentTasks.matrixTask F.toParameters (characteristic F)) reply budget q c).mp hc
    rcases MatrixMoment.EntryBits.routed_cases _ _ _ _ _ hg with hr | hh | hm
    · rw [he, hr]
      exact HT (rowQuery (characteristic F)) (IntegralCriticalFlatMomentTasks.row_parent _) _
    · rw [he, hh]
      exact HT (columnQuery (characteristic F)) (IntegralCriticalFlatMomentTasks.column_parent _) _
    · rw [he, hm]
      exact HT (matrixQuery (characteristic F)) (IntegralCriticalFlatMomentTasks.matrix_parent _) _
  refine ⟨?_, HB.2⟩
  change birth F.toParameters c < (F.rules (RankedHistoryTask.root c)).length
  rw [HB.1, (frame21 F h reply budget q c hp hc).1]
  exact hv

theorem value21 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hp : isPhase .momentEntry q) :
    (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)).value
      (answer F x) q = IntegralCriticalFlatActualMomentBits.value F q := by
  apply IntegralCriticalFlatActualMomentRoutes.program_value_local F h _ q hv
  intro hr
  have HC := ((IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
    (characteristicAccess F h)).requests_iff (answer F x) (fun _ => 1) q _).mpr ⟨hr, rfl⟩
  obtain ⟨HV, HP⟩ := moment_requested F h _ _ q _ hv hp HC
  exact hx.action _ HV HP

theorem value25 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (IntegralCriticalFlatActualCoefficientBits.program F).value (answer F x) q = IntegralCriticalTotalCreatingBits.coefficientValue F q := by
  apply IntegralCriticalFlatActualCoefficientBits.value
  intro _
  exact (hx.relativePower _ (next_valid F .relativePower q hv) (IntegralCriticalFlatEulerBits.next_phase _ _ _)).trans
    (IntegralCriticalTotalSnapshotBits.action_next_value F .relativePower q)

theorem value26 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) (q : List Bool) :
    (IntegralCriticalTotalCompanionBits.program F).value (answer F x) q = IntegralCriticalFlatHeightBits.companionValue F q := by
  apply IntegralCriticalTotalCompanionBits.program_coefficientValue
  intro c hv _
  exact (hx.coefficient _ ((IntegralCriticalTotalCompanionBits.child_valid F c).mpr hv)
    (IntegralCriticalTotalCompanionBits.child_phase F c)).trans (IntegralCriticalTotalCreatingBits.coefficientValue_eq F _)

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits
