/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarContextModels
/-! # Internal scalar requests use only the current full scalar model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → phase q ≤ 5 → answer q = (machine P a D h).model q

theorem physical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D) answer := by
  intro p q hp hv hr hx hphase
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by omega
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hphase, HX⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model0 P a D h q HS).trans (IntegralMixedFullScalarLeadingBits.physical_value P D q))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model1 P a D h q HS).trans (denominator_physical P a D h q HS hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model3 P a D h q HS).trans (scalar_physical P a D h .commonLeading q HS hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model4 P a D h q HS).trans (IntegralMixedNativeHeightActualBits.physical_model P D q hx))

theorem virtual_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D) answer := by
  intro p q hp hv hr hx hphase
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by have := hx.1; omega, hx.2⟩
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hphase, HX⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model0 P a D h q HS).trans (IntegralMixedFullScalarLeadingBits.virtual_value P D q))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model1 P a D h q HS).trans (denominator_virtual P a D h q hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model3 P a D h q HS).trans (scalar_virtual P a D h .commonLeading q hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model4 P a D h q HS).trans (IntegralMixedNativeHeightActualBits.virtual_model P D q hx))

theorem height_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedHeightCurrentBits.Matches P D answer := by
  constructor
  intro q hs hx
  have H := (IntegralMixedNativeOldHeightBits.selected_iff P q).mp hs
  have HS := (selected_iff P .clearedHeight q).mpr ⟨H.1, H.2.1, H.2.2, hx⟩
  exact (hm q H.1 H.2.1 hx (by rw [H.2.2]; decide)).trans (model2 P a D h q HS)

theorem replies_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : Replies P D answer :=
  ⟨physical_matches P a D h answer hm, virtual_matches P a D h answer hm, height_matches P a D h answer hm⟩

theorem correct_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer) (hm : Matches P a D h answer) :
    Correct (machine P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D h answer hp (replies_of_matches P a D h answer hm)
end LeanCanny.Algebra.IntegralMixedFullScalarBits
