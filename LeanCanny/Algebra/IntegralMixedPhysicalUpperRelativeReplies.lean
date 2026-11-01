/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalUpperFiniteReplies
/-! # Physical relative-factor children retain their selected source context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits IntegralMixedPhysicalComponentBits IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

theorem relative_current (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (q : List Bool) (hq : selected P .relativeFactor q = true) :
    RelativeFactorRepliesAt P F answer q := by
  have H := selected_base P .relativeFactor q hq
  have HX := ((IntegralMixedPhysicalContextBits.selected_iff P .relativeFactor q).mp hq).2
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have HP : original (diagonalQuery (characteristic P F) (outer23 P F q)) = q :=
      (IntegralCriticalFlatRelativeFactorBits.diagonal_original _ _).trans (outer23_parent P F q)
    change answer (IntegralCriticalFlatMatrixQuery.writer P .actionEntry
      (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic P F) (diagonalQuery (characteristic P F) (outer23 P F q)))) = _
    exact matrix P F answer hm .actionEntry (by decide) _
      (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]; exact H.1)
      (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]; exact H.2.1)
      (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]; exact HX)
  · apply current P F answer hm .momentPower (by decide) q _
    · exact (IntegralCriticalFlatBerkowitzQuery.momentWriter_root P _).trans
        (congrArg RankedHistoryTask.root (outer23_parent P F q))
    · exact (IntegralCriticalFlatBerkowitzQuery.momentWriter_birth P _).trans
        (congrArg (birth P) (outer23_parent P F q))
    · unfold momentChild23 IntegralMixedRoutineTaskBits.routine
      simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false, outer23_parent]
    · unfold momentChild23
      simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false, outer23_parent]
    · exact H.1
    · exact H.2.1
    · exact HX
    · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_phase P _

theorem replies (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (hl : LeadingCallback P F answer) :
    IntegralMixedPhysicalUpperDispatcherBits.Replies P a F h answer where
  entry q hq := entry_current P F answer hm hl q ((selectedFinite_iff P .reductionEntry _ q).mp hq).1
  reduction q hq := reduction_current P F answer hm q hq
  power q hq := power_current P F answer hm q ((selectedFinite_iff P .actionEntry _ q).mp hq).1
  action q hq := action_current P a F h answer hm q hq
  momentEntry q hq := moment_current P F g answer hm q hq
  relative q hq := relative_current P F answer hm q ((selectedFinite_iff P .relativeFactor _ q).mp hq).1
  factor q hq := factor_current P F g answer hm q hq
  coefficient q hq := coefficient_current P F answer hm hl q hq

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P F (fun q => residueBits (x q)))
    (hl : LeadingCallback P F (fun q => residueBits (x q))) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalUpperDispatcherBits.machine P a F h)
      (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalUpperDispatcherBits.correct P a F h g x (replies P a F h g _ hm hl)
end LeanCanny.Algebra.IntegralMixedPhysicalUpperReplyBits
