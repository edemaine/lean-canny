/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalDispatcher
/-! # Physical arithmetic callbacks from actual current scalar components

This is semantic matching only. In particular, the denominator and leading
components carry no FP or SpaceFunction assumption.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits
set_option backward.isDefEq.respectTransparency false

noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .originalCoefficient => IntegralMixedPhysicalContextBits.originalLeadingValue P F
  | .derivativeCoefficient => IntegralMixedPhysicalDenominatorBits.value P F
  | .monomialFactor => IntegralMixedPhysicalUpperBits.commonLeading P F
  | .factorPower => IntegralMixedPhysicalNativeLowerBits.height P F
  | _ => fun _ => []

def allowed (p : Phase) : Prop := p = .originalCoefficient ∨ p = .derivativeCoefficient ∨ p = .monomialFactor ∨ p = .factorPower

abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ p q, allowed p → IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    get P .slot15 q = 1 → isPhase p q → answer q = component P F p q

theorem query_match (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (p : Phase) (q : List Bool) (hp : allowed p)
    (hv : IntegralMixedVirtualCaps.valid P q) (hx : get P .slot15 q = 1) :
    answer (IntegralMixedRoutineTaskBits.query P (birth P) .scalar p q) =
      component P F p (IntegralMixedRoutineTaskBits.query P (birth P) .scalar p q) := by
  apply hm p _ hp
  · unfold IntegralMixedVirtualCaps.valid
    rw [IntegralMixedRoutineTaskBits.query_birth P (birth P) .scalar p q (min_le_right _ _),
      IntegralMixedRoutineTaskBits.query_root]
    exact hv
  · exact IntegralMixedRoutineTaskBits.query_routine P (birth P) .scalar p q
  · rw [IntegralMixedRoutineTaskBits.query_get]
    exact hx
  · exact IntegralMixedRoutineTaskBits.query_phase P (birth P) .scalar p q

theorem leading_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPhysicalContextBits.originalLeadingValue P F (IntegralMixedScalarQueryBits.originalLeading P q) =
      IntegralMixedPhysicalContextBits.originalLeadingValue P F q := by
  have HL (c : List Bool) : (IntegralMixedPhysicalNativeLowerBits.source P F).leading c =
      (F.spatial (IntegralMixedPhysicalTaskBits.saved P c)).leading :=
    IntegralMixedPhysicalCriticalBits.leading_eq (IntegralMixedPhysicalTaskBits.family P F)
      (IntegralMixedPhysicalTaskBits.indices P F) c
  simp only [IntegralMixedPhysicalContextBits.originalLeadingValue, HL]
  unfold IntegralMixedScalarQueryBits.originalLeading
  have HS : IntegralMixedPhysicalTaskBits.saved P (IntegralMixedRoutineTaskBits.query P (birth P) .scalar .originalCoefficient q) =
      IntegralMixedPhysicalTaskBits.saved P q := IntegralMixedRoutineTaskBits.query_saved P .scalar .originalCoefficient q
  have HM : modulus P (IntegralMixedRoutineTaskBits.query P (birth P) .scalar .originalCoefficient q) = modulus P q := by
    unfold modulus
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (congrArg (fun key => (F.spatial key).leading) HS) HM

theorem lower_callbacks (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) : IntegralMixedPhysicalContextLowerReplyBits.Callbacks P F answer where
  denominator q hv _ hx := query_match P F answer hm .derivativeCoefficient q (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) hv hx
  height q hv _ hx := query_match P F answer hm .factorPower q (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) hv hx
  leading q hv _ hx := (query_match P F answer hm .originalCoefficient q (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) hv hx).trans (leading_child P F q)

theorem upper_callback (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) : IntegralMixedPhysicalUpperReplyBits.LeadingCallback P F answer := by
  intro q hq
  have H : IntegralMixedVirtualCaps.valid P q ∧ get P .slot15 q = 1 := by
    rcases hq with hq | hq
    · exact ⟨(IntegralMixedPhysicalUpperBits.selected_base P .criticalCoefficient q hq).1,
        ((IntegralMixedPhysicalContextBits.selected_iff P .criticalCoefficient q).mp hq).2⟩
    · exact ⟨(IntegralMixedPhysicalUpperBits.selected_base P .reductionEntry q hq).1,
        ((IntegralMixedPhysicalContextBits.selected_iff P .reductionEntry q).mp hq).2⟩
  exact query_match P F answer hm .monomialFactor q (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) H.1 H.2

theorem dispatcher_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P F))
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : IntegralMixedPhysicalComponentBits.Matches P F (fun q => residueBits (x q)))
    (hs : Matches P F (fun q => residueBits (x q))) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalDispatcherBits.machine P a F h ha)
      (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalDispatcherBits.correct P a F h ha g x hm (lower_callbacks P F _ hs) (upper_callback P F _ hs)
end LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyBits
