/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarContextModels
/-! # Internal scalar requests use only the current full scalar model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → phase q ≤ 5 → answer q = (machine P a D J h).model q

theorem physical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) :
    IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D J) answer := by
  intro p q hp hv hr hx hphase
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by omega
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hphase, HX⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model0 P a D J h q HS).trans (IntegralMixedFramedScalarLeadingBits.physical_value P D J q))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model1 P a D J h q HS).trans (denominator_physical P a D J h q HS hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model3 P a D J h q HS).trans (scalar_physical P a D J h .commonLeading q HS hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model4 P a D J h q HS).trans (IntegralMixedFramedNativeHeightActualBits.physical_model P D J q hx))

theorem virtual_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) :
    IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D J) answer := by
  intro p q hp hv hr hx hphase
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by have := hx.1; omega, hx.2⟩
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hphase, HX⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model0 P a D J h q HS).trans (IntegralMixedFramedScalarLeadingBits.virtual_value P D J q))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model1 P a D J h q HS).trans (denominator_virtual P a D J h q hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model3 P a D J h q HS).trans (scalar_virtual P a D J h .commonLeading q hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model4 P a D J h q HS).trans (IntegralMixedFramedNativeHeightActualBits.virtual_model P D J q hx))

theorem height_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) : IntegralMixedFramedHeightCurrentBits.Matches P D J answer := by
  constructor
  intro q hs hx
  have H := (IntegralMixedFramedNativeOldHeightBits.selected_iff P q).mp hs
  have HS := (selected_iff P .clearedHeight q).mpr ⟨H.1, H.2.1, H.2.2, hx⟩
  exact (hm q H.1 H.2.1 hx (by rw [H.2.2]; decide)).trans (model2 P a D J h q HS)

theorem replies_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) : Replies P D J answer :=
  ⟨physical_matches P a D J h answer hm, virtual_matches P a D J h answer hm, height_matches P a D J h answer hm⟩

theorem correct_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (hm : Matches P a D J h answer) :
    Correct (machine P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D J h answer hp (replies_of_matches P a D J h answer hm)
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
