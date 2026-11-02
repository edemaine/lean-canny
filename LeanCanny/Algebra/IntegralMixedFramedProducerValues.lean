/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionActual
/-! # The full native producer dispatcher closes literal old-bank recursive replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

theorem model_leading (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6)
    (hx : get P .slot15 q ≤ 4) (hp : phase q = 0) :
    (machine P a D H h).model q = IntegralMixedFramedProducerActualBits.leading P D H q := by
  by_cases h0 : get P .slot15 q = 0
  · rw [model_integer P a D H h q hv hr h0, IntegralMixedFramedProducerActualBits.leading, ite_eq_left h0]
    exact IntegralMixedIntegerFamilyBits.model_leading P a (virtualFamily P D H) (virtualInput P a D H h) (IntegralMixedFramedIntegerBits.polynomial P D) h.integer q
      ((IntegralMixedIntegerProducerBits.selected_iff P .originalCoefficient q).mpr ⟨hv, hr, hp, h0⟩)
  · by_cases h1 : get P .slot15 q = 1
    · rw [model_physical P a D H h q hv hr h1, IntegralMixedFramedProducerActualBits.leading, ite_eq_right h0, ite_eq_left h1]
      exact IntegralMixedPhysicalCompanionDispatcherBits.model_leading P a _ (physicalInput P a D H h) q
        ((IntegralMixedPhysicalProducerLeadingBits.selected_iff P q).mpr ⟨hv, hr, hp, h1⟩)
    · have hl : 2 ≤ get P .slot15 q := by omega
      rw [model_cut P a D H h q hv hr hl hx, IntegralMixedFramedProducerActualBits.leading, ite_eq_right h0, ite_eq_right h1]
      exact IntegralMixedNormalizedCompanionDispatcherBits.model_leading P a _
        (virtualInput P a D H h) (degreeInput P a D H h) q
        ((IntegralMixedNormalizedCompanionBits.selected_iff P .originalCoefficient q).mpr ⟨hv, hr, hp, hl, hx⟩)

theorem model_companion (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6)
    (hx : get P .slot15 q ≤ 4) (hp : phase q = 26) :
    (machine P a D H h).model q = IntegralMixedFramedProducerActualBits.companion P D H q := by
  by_cases h0 : get P .slot15 q = 0
  · rw [model_integer P a D H h q hv hr h0, IntegralMixedFramedProducerActualBits.companion, ite_eq_left h0]
    exact IntegralMixedIntegerFamilyBits.model_companion P a (virtualFamily P D H) (virtualInput P a D H h) (IntegralMixedFramedIntegerBits.polynomial P D) h.integer q
      ((IntegralMixedIntegerProducerBits.selected_iff P .companion q).mpr ⟨hv, hr, hp, h0⟩)
  · by_cases h1 : get P .slot15 q = 1
    · rw [model_physical P a D H h q hv hr h1, IntegralMixedFramedProducerActualBits.companion, ite_eq_right h0, ite_eq_left h1]
      exact IntegralMixedPhysicalCompanionDispatcherBits.model_companion P a _ (physicalInput P a D H h) q
        ((IntegralMixedPhysicalCompanionBits.selected_iff P q).mpr ⟨hv, hr, hp, h1⟩)
    · have hl : 2 ≤ get P .slot15 q := by omega
      rw [model_cut P a D H h q hv hr hl hx, IntegralMixedFramedProducerActualBits.companion, ite_eq_right h0, ite_eq_right h1]
      exact IntegralMixedNormalizedCompanionDispatcherBits.model_companion P a _
        (virtualInput P a D H h) (degreeInput P a D H h) q
        ((IntegralMixedNormalizedCompanionBits.selected_iff P .companion q).mpr ⟨hv, hr, hp, hl, hx⟩)

theorem producer_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) : IntegralMixedFramedProducerActualBits.Matches P D H answer where
  leading q hv hr hx hp := (hm q hv hr).trans (model_leading P a D H h q hv hr hx hp)
  companion q hv hr hx hp := (hm q hv hr).trans (model_companion P a D H h q hv hr hx hp)

end LeanCanny.Algebra.IntegralMixedFramedProducerBits
