/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalDispatcher
/-! # Critical replies close internally over the literal source-framed bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

abbrev Matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → answer q = (machine P a D H h).model q

theorem physical_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedPhysicalComponentBits.Matches P (physicalFamily P D H) answer := by
  intro p q hp hs
  have ht : IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q ∧ get P .slot15 q = 1 :=
    of_decide_eq_true hs
  exact ((hm q ht.1 ht.2.1).trans (model_physical P a D H h q ht.1 ht.2.1 ht.2.2.2)).trans
    (IntegralMixedPhysicalDispatcherBits.model_phase P a _ (physicalInput P a D H h) h.physicalOriginal p q hp ht.1 ht.2.1 ht.2.2.2 ht.2.2.1)

theorem virtual_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedVirtualContextComponentBits.Matches P (virtualFamily P D H) answer := by
  intro p q hp hs
  have ht : IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q ∧ IntegralMixedVirtualContextBits.context P q :=
    of_decide_eq_true hs
  exact ((hm q ht.1 ht.2.1).trans (model_virtual P a D H h q ht.1 ht.2.1 ht.2.2.2.1 ht.2.2.2.2)).trans
    (IntegralMixedVirtualContextDispatcherBits.model_phase P a _
      (virtualInput P a D H h) h.virtualOriginal p q hp ht.1 ht.2.1 ht.2.2.2 ht.2.2.1)

theorem correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a D H h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D H) (fun q => residueBits (x q)))
    (hv : IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D H) (fun q => residueBits (x q))) :
    Correct (machine P a D H h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply IntegralMixedRoutineContextGuard.correct
    · exact IntegralMixedPhysicalScalarReplyBits.dispatcher_correct P a _ (physicalInput P a D H h) h.physicalOriginal
        (IntegralMixedFramedPhysicalBits.geometry P D H) x
        (physical_matches P a D H h _ hm) hp
    · exact physical_selected P a D H h
  · apply choose_correct
    · apply IntegralMixedRoutineContextGuard.correct
      · exact IntegralMixedVirtualContextScalarReplyBits.dispatcher_correct P a _
          (virtualInput P a D H h) h.virtualOriginal
          (IntegralMixedFramedHistoryFamilyBits.geometry P D H) x (virtual_matches P a D H h _ hm) hv
      · exact virtual_selected P a D H h
    · exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedFramedCriticalBits
