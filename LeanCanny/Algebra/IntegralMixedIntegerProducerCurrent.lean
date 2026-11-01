/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerDispatcher
/-! # Integer companion replies close against one current original-data model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedIntegerProducerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 →
    get P .slot15 q = 0 → answer q = (machine P a D h c).model q

theorem coefficient_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (answer : List Bool → List Bool)
    (hm : Matches P a D h c answer) : CoefficientMatches P D answer := by
  intro q hq
  have HQ := (selected_iff P .criticalCoefficient q).mp hq
  exact (hm q HQ.1 HQ.2.1 HQ.2.2.2).trans (model_coefficient P a D h c q hq)

theorem leading_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (answer : List Bool → List Bool)
    (hm : Matches P a D h c answer) : LeadingMatches P D answer := by
  intro q hq
  have HQ := (selected_iff P .companion q).mp hq
  let child := leadingChild P q
  have HB : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
  have HV : IntegralMixedVirtualCaps.valid P child := by
    unfold IntegralMixedVirtualCaps.valid child leadingChild
    rw [IntegralMixedRoutineTaskBits.query_birth P _ .companion .originalCoefficient q HB,
      IntegralMixedRoutineTaskBits.query_root]
    exact HQ.1
  have HR : IntegralMixedRoutineTaskBits.routine P child = 6 :=
    IntegralMixedRoutineTaskBits.query_routine P _ .companion .originalCoefficient q
  have HP : isPhase .originalCoefficient child := IntegralMixedRoutineTaskBits.query_phase P _ .companion .originalCoefficient q
  have HX : get P .slot15 child = 0 := by
    unfold child leadingChild
    rw [IntegralMixedRoutineTaskBits.query_get]
    exact HQ.2.2.2
  have HS : selected P .originalCoefficient child = true := (selected_iff P .originalCoefficient child).mpr ⟨HV, HR, HP, HX⟩
  have HE := (hm child HV HR HX).trans (model_leading P a D h c child HS)
  have HSaved : IntegralMixedVirtualTaskBits.saved P child = IntegralMixedVirtualTaskBits.saved P q :=
    IntegralMixedRoutineTaskBits.query_saved P .companion .originalCoefficient q
  have HMod : modulus P child = modulus P q := by
    unfold modulus child leadingChild
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  apply HE.trans
  change leadingValue P D child = leadingValue P D q
  unfold leadingValue leadingInteger
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (congrArg (fun key => (polynomial P D key).leadingCoeff) HSaved) HMod

theorem correct_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a D h c (fun q => residueBits (x q))) :
    Correct (machine P a D h c) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D h c x (coefficient_matches P a D h c _ hm) (leading_matches P a D h c _ hm)

theorem coefficient_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = coefficientValue P D q := by
  unfold coefficientValue
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

theorem leading_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = leadingValue P D q := ⟨_, rfl⟩

attribute [local irreducible] leadingValue coefficientValue companionValue

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h c).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if selected P .originalCoefficient q then leadingValue P D q else
      if selected P .criticalCoefficient q then coefficientValue P D q else
        if selected P .companion q then companionValue P D q else []
  cases hlead : selected P .originalCoefficient q
  · rw [ite_eq_right (by decide)]
    cases hcoeff : selected P .criticalCoefficient q
    · rw [ite_eq_right (by decide)]
      cases hcomp : selected P .companion q
      · rw [ite_eq_right (by decide)]
        exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
      · rw [ite_eq_left rfl]
        exact companionValue_canonical P D q
    · rw [ite_eq_left rfl]
      exact coefficient_canonical P D q
  · rw [ite_eq_left rfl]
    exact leading_canonical P D q

end LeanCanny.Algebra.IntegralMixedIntegerProducerDispatcherBits
