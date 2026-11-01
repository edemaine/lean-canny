/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcher
/-! # The joint current model closes critical-to-producer arithmetic replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q →
    (IntegralMixedRoutineTaskBits.routine P q = 1 ∨ IntegralMixedRoutineTaskBits.routine P q = 6) → answer q = (machine P a D h).model q

theorem critical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedFullCriticalDispatcherBits.Matches P a D h.critical answer := by
  intro q hv hr
  exact (hm q hv (Or.inl hr)).trans (model_critical P a D h q hr)

theorem producer_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedFullProducerDispatcherBits.Matches P a D h.producer answer := by
  intro q hv hr
  exact (hm q hv (Or.inr hr)).trans (model_producer P a D h q hr)

theorem node_correct (P : Parameters) (a : Access P) (code : ℕ) (M : Machine)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hm : Correct M answer frame) (hs : ∀ q, M.selected q = true) : Correct (node P a code M).machine answer frame :=
  withGuard_correct M _ _ answer frame hm (fun q _ => hs q)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q)))
    (hp : IntegralMixedPhysicalScalarReplyBits.Matches P (IntegralMixedFullCriticalDispatcherBits.physicalFamily P D) (fun q => residueBits (x q)))
    (hv : IntegralMixedVirtualContextScalarReplyBits.Matches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.NormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · apply node_correct
    · exact IntegralMixedFullCriticalDispatcherBits.correct P a D h.critical x (critical_matches P a D h _ hm) hp hv
    · exact IntegralMixedFullCriticalDispatcherBits.selected P a D h.critical
  · rcases List.mem_cons.mp hb with rfl | hb
    · apply node_correct
      · exact IntegralMixedFullProducerDispatcherBits.correct P a D h.producer x (producer_matches P a D h _ hm)
          (IntegralMixedFullCriticalDispatcherBits.physical_matches P a D h.critical _ (critical_matches P a D h _ hm)) hp hn
      · exact IntegralMixedFullProducerDispatcherBits.selected P a D h.producer
    · cases hb

theorem old_height_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    Correct (IntegralMixedFullOldHeightBits.machine P a D h.producer.full) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFullProducerDispatcherBits.old_height_correct P a D h.producer answer (producer_matches P a D h answer hm)

end LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
