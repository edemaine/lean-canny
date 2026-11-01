/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionDispatcher
/-! # A single current physical companion model closes producer-leading callbacks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCompanionDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalCompanionBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 →
    get P .slot15 q = 1 → answer q = (machine P a F h).model q

theorem leading_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (answer : List Bool → List Bool)
    (hm : Matches P a F h answer) : LeadingMatches P F answer := by
  intro q hq
  have HQ := (selected_iff P q).mp hq
  let c := leadingChild P q
  have HB : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c leadingChild
    rw [IntegralMixedRoutineTaskBits.query_birth P _ .companion .originalCoefficient q HB,
      IntegralMixedRoutineTaskBits.query_root]
    exact HQ.1
  have HR : IntegralMixedRoutineTaskBits.routine P c = 6 :=
    IntegralMixedRoutineTaskBits.query_routine P _ .companion .originalCoefficient q
  have HP : isPhase .originalCoefficient c := IntegralMixedRoutineTaskBits.query_phase P _ .companion .originalCoefficient q
  have HX : get P .slot15 c = 1 := by
    unfold c leadingChild
    rw [IntegralMixedRoutineTaskBits.query_get]
    exact HQ.2.2.2
  have HS : IntegralMixedPhysicalProducerLeadingBits.selected P c = true :=
    (IntegralMixedPhysicalProducerLeadingBits.selected_iff P c).mpr ⟨HV, HR, HP, HX⟩
  have HE := (hm c HV HR HX).trans (model_leading P a F h c HS)
  have HSaved : IntegralMixedPhysicalTaskBits.saved P c = IntegralMixedPhysicalTaskBits.saved P q :=
    IntegralMixedRoutineTaskBits.query_saved P .companion .originalCoefficient q
  have HMod : modulus P c = modulus P q := by
    unfold modulus c leadingChild
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  apply HE.trans
  change IntegralMixedPhysicalProducerLeadingBits.value P F c =
    residueBits (IntegralClearedCriticalLeadingBits.integer (IntegralMixedPhysicalUpperBits.critical P F) q : ZMod (modulus P q))
  rw [IntegralMixedPhysicalProducerLeadingBits.value_actual, IntegralMixedPhysicalProducerLeadingBits.integer_actual]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (congrArg (fun key => IntegralMixedHistory.criticalLeading (F.state key) (F.birth_bound key) (F.rule key)) HSaved) HMod

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hc : IntegralMixedPhysicalComponentBits.Matches P F (fun q => residueBits (x q)))
    (hs : IntegralMixedPhysicalScalarReplyBits.Matches P F (fun q => residueBits (x q)))
    (hm : Matches P a F h (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g x (critical_matches P F _ hc) (leading_matches P a F h _ hm) hs

attribute [local irreducible] IntegralMixedPhysicalProducerLeadingBits.value companionValue

theorem canonical (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if IntegralMixedPhysicalProducerLeadingBits.selected P q then IntegralMixedPhysicalProducerLeadingBits.value P F q else
      if selected P q then companionValue P F q else []
  cases hlead : IntegralMixedPhysicalProducerLeadingBits.selected P q
  · rw [ite_eq_right (by decide)]
    cases hcomp : selected P q
    · rw [ite_eq_right (by decide)]
      exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
    · rw [ite_eq_left rfl]
      exact companionValue_canonical P F q
  · rw [ite_eq_left rfl]
    exact IntegralMixedPhysicalProducerLeadingBits.canonical P F q

end LeanCanny.Algebra.IntegralMixedPhysicalCompanionDispatcherBits
