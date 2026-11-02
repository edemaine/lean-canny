/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeDispatcher
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarUnitControls
/-! # Every framed arithmetic callback uses the same current native model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → answer q = (machine P a D H h).model q

theorem component_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer)
    (r : Fin 7) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = r.val) : answer q = (component P a D H h r).model q :=
  (hm q hv).trans (model_component P a D H h r q hr)

theorem scalar_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedFullScalarBits.Matches P a D H h.scalar answer := by
  intro q hv hr hx hp
  have HE := component_matches P a D H h answer hm 0 q hv hr
  simpa only [component] using HE

theorem critical_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedCriticalBits.Matches P a D H h.critical answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 1 q hv hr
  simpa only [component] using HE

theorem entry_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedEntryBits.Matches P a D H h.critical answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 2 q hv hr
  simpa only [component] using HE

theorem determinant_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedDeterminantBits.Matches P a D H h.critical answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 3 q hv hr
  simpa only [component] using HE

theorem raw_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedNormalizationBits.RawMatches P a D H h.normalization answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 4 q hv hr
  simpa only [component, IntegralMixedFramedNormalizationBits.rawMachine] using HE

theorem normalization_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedNormalizationBits.Matches P a D H h.normalization answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 5 q hv hr
  simpa only [component] using HE

theorem producer_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedProducerBits.Matches P a D H h.producer answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 6 q hv hr
  simpa only [component] using HE

theorem producer_actual (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedProducerActualBits.Matches P D H answer :=
  IntegralMixedFramedProducerBits.producer_matches P a D H h.producer answer (producer_matches P a D H h answer hm)

theorem scalar_semantic (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedScalarModelBits.Matches P D H answer :=
  IntegralMixedFramedFullScalarBits.semantic_matches P a D H h.scalar answer (scalar_matches P a D H h answer hm)

end LeanCanny.Algebra.IntegralMixedFramedNativeBits
