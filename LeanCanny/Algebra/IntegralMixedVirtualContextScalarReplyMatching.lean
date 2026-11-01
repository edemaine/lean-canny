/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextDispatcher
/-! # Virtual arithmetic callbacks from actual current scalar components

This is semantic matching only. In particular, the denominator and leading
components carry no FP or SpaceFunction assumption.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
set_option backward.isDefEq.respectTransparency false

noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .originalCoefficient => IntegralMixedVirtualContextBits.originalLeadingValue P F
  | .derivativeCoefficient => IntegralMixedVirtualDenominatorBits.value P F
  | .monomialFactor => IntegralMixedVirtualContextUpperBits.commonLeading P F
  | .factorPower => IntegralMixedVirtualNativeLowerBits.height P F
  | _ => fun _ => []

def allowed (p : Phase) : Prop := p = .originalCoefficient ∨ p = .derivativeCoefficient ∨ p = .monomialFactor ∨ p = .factorPower

abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ p q, allowed p → IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    IntegralMixedVirtualContextBits.context P q → isPhase p q → answer q = component P F p q

theorem query_match (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (p : Phase) (q : List Bool) (hp : allowed p)
    (hv : IntegralMixedVirtualCaps.valid P q) (hx : IntegralMixedVirtualContextBits.context P q) :
    answer (IntegralMixedRoutineTaskBits.query P (birth P) .scalar p q) =
      component P F p (IntegralMixedRoutineTaskBits.query P (birth P) .scalar p q) := by
  apply hm p _ hp
  · unfold IntegralMixedVirtualCaps.valid
    rw [IntegralMixedRoutineTaskBits.query_birth P (birth P) .scalar p q (min_le_right _ _),
      IntegralMixedRoutineTaskBits.query_root]
    exact hv
  · exact IntegralMixedRoutineTaskBits.query_routine P (birth P) .scalar p q
  · unfold IntegralMixedVirtualContextBits.context
    rw [IntegralMixedRoutineTaskBits.query_get]
    exact hx
  · exact IntegralMixedRoutineTaskBits.query_phase P (birth P) .scalar p q

theorem leading_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualContextBits.originalLeadingValue P F (IntegralMixedScalarQueryBits.originalLeading P q) =
      IntegralMixedVirtualContextBits.originalLeadingValue P F q := by
  have HL (c : List Bool) : (IntegralMixedVirtualNativeLowerBits.source P F).leading c =
      (F.spatial (IntegralMixedVirtualTaskBits.saved P c)).leading :=
    rfl
  simp only [IntegralMixedVirtualContextBits.originalLeadingValue, HL]
  unfold IntegralMixedScalarQueryBits.originalLeading
  have HS : IntegralMixedVirtualTaskBits.saved P (IntegralMixedRoutineTaskBits.query P (birth P) .scalar .originalCoefficient q) =
      IntegralMixedVirtualTaskBits.saved P q := IntegralMixedRoutineTaskBits.query_saved P .scalar .originalCoefficient q
  have HM : modulus P (IntegralMixedRoutineTaskBits.query P (birth P) .scalar .originalCoefficient q) = modulus P q := by
    unfold modulus
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (congrArg (fun key => (F.spatial key).leading) HS) HM

theorem lower_callbacks (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) : IntegralMixedVirtualContextLowerReplyBits.Callbacks P F answer where
  denominator q hv _ hx := query_match P F answer hm .derivativeCoefficient q (by unfold IntegralMixedVirtualContextScalarReplyBits.allowed; decide) hv hx
  height q hv _ hx := query_match P F answer hm .factorPower q (by unfold IntegralMixedVirtualContextScalarReplyBits.allowed; decide) hv hx
  leading q hv _ hx := (query_match P F answer hm .originalCoefficient q (by unfold IntegralMixedVirtualContextScalarReplyBits.allowed; decide) hv hx).trans (leading_child P F q)

theorem upper_callback (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) : IntegralMixedVirtualContextUpperReplyBits.LeadingCallback P F answer := by
  intro q hq
  have H : IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q := by
    rcases hq with hq | hq
    · exact ⟨(IntegralMixedVirtualContextUpperBits.selected_base P .criticalCoefficient q hq).1,
        ((IntegralMixedVirtualContextBits.selected_iff P .criticalCoefficient q).mp hq).2⟩
    · exact ⟨(IntegralMixedVirtualContextUpperBits.selected_base P .reductionEntry q hq).1,
        ((IntegralMixedVirtualContextBits.selected_iff P .reductionEntry q).mp hq).2⟩
  exact query_match P F answer hm .monomialFactor q (by unfold IntegralMixedVirtualContextScalarReplyBits.allowed; decide) H.1 H.2

theorem dispatcher_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P F))
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : IntegralMixedVirtualContextComponentBits.Matches P F (fun q => residueBits (x q)))
    (hs : Matches P F (fun q => residueBits (x q))) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextDispatcherBits.machine P a F h ha)
      (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextDispatcherBits.correct P a F h ha g x hm (lower_callbacks P F _ hs) (upper_callback P F _ hs)
end LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyBits
