/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCriticalDispatcher
/-! # Internal critical arithmetic replies close in both actual producer contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → answer q = (machine P a D h).model q

theorem physical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedPhysicalComponentBits.Matches P (physicalFamily P D) answer := by
  intro p q hp hs
  have ht : IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q ∧ get P .slot15 q = 1 :=
    of_decide_eq_true hs
  exact ((hm q ht.1 ht.2.1).trans (model_physical P a D h q ht.1 ht.2.1 ht.2.2.2)).trans
    (IntegralMixedPhysicalDispatcherBits.model_phase P a _ h.physical h.physicalOriginal p q hp ht.1 ht.2.1 ht.2.2.2 ht.2.2.1)

theorem virtual_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedVirtualContextComponentBits.Matches P (IntegralMixedFullHistoryFamilyBits.family P D) answer := by
  intro p q hp hs
  have ht : IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q ∧ IntegralMixedVirtualContextBits.context P q :=
    of_decide_eq_true hs
  exact ((hm q ht.1 ht.2.1).trans (model_virtual P a D h q ht.1 ht.2.1 ht.2.2.2.1 ht.2.2.2.2)).trans
    (IntegralMixedVirtualContextDispatcherBits.model_phase P a _
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.virtualOriginal p q hp ht.1 ht.2.1 ht.2.2.2 ht.2.2.1)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a D h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D) (fun q => residueBits (x q)))
    (hv : IntegralMixedVirtualContextScalarReplyBits.Matches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply IntegralMixedRoutineContextGuard.correct
    · exact IntegralMixedPhysicalScalarReplyBits.dispatcher_correct P a _ h.physical h.physicalOriginal
        (IntegralMixedFullPhysicalBits.geometry P (IntegralMixedFullHistoryFamilyBits.physicalData P D)) x
        (physical_matches P a D h _ hm) hp
    · exact physical_selected P a D h
  · apply choose_correct
    · apply IntegralMixedRoutineContextGuard.correct
      · exact IntegralMixedVirtualContextScalarReplyBits.dispatcher_correct P a _
          (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.virtualOriginal
          (IntegralMixedFullHistoryFamilyBits.geometry P D) x (virtual_matches P a D h _ hm) hv
      · exact virtual_selected P a D h
    · exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
