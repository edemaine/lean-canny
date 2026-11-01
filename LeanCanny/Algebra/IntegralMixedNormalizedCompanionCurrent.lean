/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcher
/-! # One current normalized-companion model closes its producer-leading replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizedCompanionBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 →
    2 ≤ get P .slot15 q → get P .slot15 q ≤ 4 → answer q = (machine P a F h hd).model q

theorem leading_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (answer : List Bool → List Bool)
    (hm : Matches P a F h hd answer) : LeadingMatches P F answer := by
  intro q hq
  have HQ := (selected_iff P .companion q).mp hq
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
  have HX : get P .slot15 c = get P .slot15 q := by
    unfold c leadingChild
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  have HL : 2 ≤ get P .slot15 c := by rw [HX]; exact HQ.2.2.2.1
  have HU : get P .slot15 c ≤ 4 := by rw [HX]; exact HQ.2.2.2.2
  have HS : selected P .originalCoefficient c = true := (selected_iff P .originalCoefficient c).mpr ⟨HV, HR, HP, HL, HU⟩
  have HE := (hm c HV HR HL HU).trans (model_leading P a F h hd c HS)
  have HSaved : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q :=
    IntegralMixedRoutineTaskBits.query_saved P .companion .originalCoefficient q
  have HMod : modulus P c = modulus P q := by
    unfold modulus c leadingChild
    rw [IntegralMixedRoutineTaskBits.query_get]
    rfl
  apply HE.trans
  unfold IntegralMixedNormalizationTopBits.leadingValue
  rw [HSaved, HMod]
  rfl

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hn : NormalizationMatches P F (fun q => residueBits (x q)))
    (hm : Matches P a F h hd (fun q => residueBits (x q))) :
    Correct (machine P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h hd g x hn (leading_matches P a F h hd _ hm)

attribute [local irreducible] IntegralMixedNormalizationTopBits.leadingValue companionValue

theorem canonical (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h hd).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if selected P .originalCoefficient q then IntegralMixedNormalizationTopBits.leadingValue P F q else
      if selected P .companion q then companionValue P F q else []
  cases hs : selected P .originalCoefficient q
  · rw [ite_eq_right (by decide)]
    cases ht : selected P .companion q
    · rw [ite_eq_right (by decide)]
      exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
    · rw [ite_eq_left rfl]
      exact companionValue_canonical P F q
  · rw [ite_eq_left rfl]
    exact IntegralMixedNormalizationTopBits.leadingValue_canonical P F q

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcherBits
