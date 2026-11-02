/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullProducerSpaceCurrent
/-! # The full native producer dispatcher closes literal old-bank recursive replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullProducerSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical

theorem model_leading (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6)
    (hx : get P .slot15 q ≤ 4) (hp : phase q = 0) :
    (machine P a D h).model q = IntegralMixedProducerActualBits.leading P D q := by
  by_cases h0 : get P .slot15 q = 0
  · rw [model_integer P a D h q hv hr h0, IntegralMixedProducerActualBits.leading, ite_eq_left h0]
    exact IntegralMixedIntegerProducerSpaceDispatcherBits.model_leading P a D h.integer q
      ((IntegralMixedIntegerProducerBits.selected_iff P .originalCoefficient q).mpr ⟨hv, hr, hp, h0⟩)
  · by_cases h1 : get P .slot15 q = 1
    · rw [model_physical P a D h q hv hr h1, IntegralMixedProducerActualBits.leading, ite_eq_right h0, ite_eq_left h1]
      exact IntegralMixedPhysicalCompanionDispatcherBits.model_leading P a _ h.physical q
        ((IntegralMixedPhysicalProducerLeadingBits.selected_iff P q).mpr ⟨hv, hr, hp, h1⟩)
    · have hl : 2 ≤ get P .slot15 q := by omega
      rw [model_cut P a D h q hv hr hl hx, IntegralMixedProducerActualBits.leading, ite_eq_right h0, ite_eq_right h1]
      exact IntegralMixedNormalizedCompanionDispatcherBits.model_leading P a _
        (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree q
        ((IntegralMixedNormalizedCompanionBits.selected_iff P .originalCoefficient q).mpr ⟨hv, hr, hp, hl, hx⟩)

theorem model_companion (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6)
    (hx : get P .slot15 q ≤ 4) (hp : phase q = 26) :
    (machine P a D h).model q = IntegralMixedProducerActualBits.companion P D q := by
  by_cases h0 : get P .slot15 q = 0
  · rw [model_integer P a D h q hv hr h0, IntegralMixedProducerActualBits.companion, ite_eq_left h0]
    exact IntegralMixedIntegerProducerSpaceDispatcherBits.model_companion P a D h.integer q
      ((IntegralMixedIntegerProducerBits.selected_iff P .companion q).mpr ⟨hv, hr, hp, h0⟩)
  · by_cases h1 : get P .slot15 q = 1
    · rw [model_physical P a D h q hv hr h1, IntegralMixedProducerActualBits.companion, ite_eq_right h0, ite_eq_left h1]
      exact IntegralMixedPhysicalCompanionDispatcherBits.model_companion P a _ h.physical q
        ((IntegralMixedPhysicalCompanionBits.selected_iff P q).mpr ⟨hv, hr, hp, h1⟩)
    · have hl : 2 ≤ get P .slot15 q := by omega
      rw [model_cut P a D h q hv hr hl hx, IntegralMixedProducerActualBits.companion, ite_eq_right h0, ite_eq_right h1]
      exact IntegralMixedNormalizedCompanionDispatcherBits.model_companion P a _
        (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree q
        ((IntegralMixedNormalizedCompanionBits.selected_iff P .companion q).mpr ⟨hv, hr, hp, hl, hx⟩)

theorem producer_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedProducerActualBits.Matches P D answer where
  leading q hv hr hx hp := (hm q hv hr).trans (model_leading P a D h q hv hr hx hp)
  companion q hv hr hx hp := (hm q hv hr).trans (model_companion P a D h q hv hr hx hp)

theorem old_height_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    Correct (IntegralMixedFullOldHeightBits.machine P a D h.full) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedProducerActualBits.old_height_correct P a D h.full answer (producer_matches P a D h answer hm)

end LeanCanny.Algebra.IntegralMixedFullProducerSpaceBits
