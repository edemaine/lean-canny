/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarCurrentModel
public import LeanCanny.Algebra.IntegralMixedFramedUnitControls
/-! # A complete framed scalar backend from original unit-selector records -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Controls.ofUnit (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedUnitControlsBits.Controls P D J) : Controls P D J where
  tables := h.tables
  native := h.native
  represents := h.represents
  leading := IntegralMixedFramedUnitControlsBits.leading P a D J h
  physicalScales := IntegralMixedFramedUnitControlsBits.physicalScales P a D J h
  virtualScales := IntegralMixedFramedUnitControlsBits.virtualScales P a D J h
  height := IntegralMixedFramedUnitControlsBits.cells P a D J h

theorem semantic_matches (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) (own : Matches P a D J h answer) :
    IntegralMixedFramedScalarModelBits.Matches P D J answer := by
  intro p q hp hv hr hx hq
  rcases hp with hp | rfl
  · by_cases h1 : get P .slot15 q = 1
    · exact (physical_matches P a D J h answer own p q hp hv hr h1 hq).trans
        (IntegralMixedFramedScalarModelBits.component_physical P D J p q hp h1).symm
    · have h2 : IntegralMixedVirtualContextBits.context P q := ⟨by omega, hx.2⟩
      have hpv : IntegralMixedVirtualContextScalarReplyBits.allowed p := hp
      exact (virtual_matches P a D J h answer own p q hpv hv hr h2 hq).trans
        (IntegralMixedFramedScalarModelBits.component_virtual P D J p q hpv h2).symm
  · have hs := (selected_iff P .productEntry q).mpr ⟨hv, hr, hq, hx⟩
    have HE := (own q hv hr hx (by rw [hq]; decide)).trans (model5 P a D J h q hs)
    by_cases h1 : get P .slot15 q = 1
    · rw [IntegralMixedFramedScalarModelBits.component, ite_eq_left rfl, ite_eq_left h1]
      exact HE.trans (scalar_physical P a D J h .originalScale q hs h1)
    · have h2 : IntegralMixedVirtualContextBits.context P q := ⟨by omega, hx.2⟩
      rw [IntegralMixedFramedScalarModelBits.component, ite_eq_left rfl, ite_eq_right h1]
      exact HE.trans (scalar_virtual P a D J h .originalScale q h2)

theorem correct_of_unit_matches (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedUnitControlsBits.Controls P D J)
    (answer : List Bool → List Bool) (producer : IntegralMixedFramedProducerActualBits.Matches P D J answer)
    (own : Matches P a D J (Controls.ofUnit P a D J h) answer) :
    Correct (machine P a D J (Controls.ofUnit P a D J h)) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct_of_matches P a D J (Controls.ofUnit P a D J h) answer producer own
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
