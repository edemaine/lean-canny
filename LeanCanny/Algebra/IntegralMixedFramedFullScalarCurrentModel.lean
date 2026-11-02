/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarModel
public import LeanCanny.Algebra.IntegralMixedPhaseDecode
/-! # Current scalar contracts stated directly with actual component values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev ComponentMatches (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool → List Bool) : Prop :=
  ∀ (p : Phase) (q : List Bool), p.code ≤ 5 → IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → isPhase p q → answer q = component P D J p q

theorem matches_of_components (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : ComponentMatches P D J answer) : Matches P a D J h answer := by
  intro q hv hr hx hp
  let p := IntegralMixedPhaseDecode.decode (phase q)
  have HC : p.code = phase q := IntegralMixedPhaseDecode.code _ (IntegralMixedRoutineTaskBits.phase_lt q)
  have HQ : isPhase p q := IntegralMixedPhaseDecode.task q
  have HP : p.code ≤ 5 := HC.trans_le hp
  exact (hm p q HP hv hr hx HQ).trans (model_phase P a D J h p q hv hr hx HP HQ).symm

theorem components_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) : ComponentMatches P D J answer := by
  intro p q hp hv hr hx hq
  have HP : phase q ≤ 5 := hq.trans_le hp
  exact (hm q hv hr hx HP).trans (model_phase P a D J h p q hv hr hx hp hq)

theorem correct_of_components (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (hm : ComponentMatches P D J answer) :
    Correct (machine P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct_of_matches P a D J h answer hp (matches_of_components P a D J h answer hm)

noncomputable def residue (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) : ZMod (modulus P q) := Classical.choose (canonical P a D J h q)

theorem residue_value (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) : residueBits (residue P a D J h q) = (machine P a D J h).model q := Classical.choose_spec (canonical P a D J h q)
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
