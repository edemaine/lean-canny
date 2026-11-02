/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCore
/-! # Current joint arithmetic leaves only literal raw-cut replies external -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCoreBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q →
    (IntegralMixedRoutineTaskBits.routine P q = 0 ∨ IntegralMixedRoutineTaskBits.routine P q = 1 ∨
      IntegralMixedRoutineTaskBits.routine P q = 5 ∨ IntegralMixedRoutineTaskBits.routine P q = 6) → answer q = (machine P a D h).model q

theorem core_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedFullCoreBits.Matches P a D h.core answer := by
  intro q hv hr
  have h5 : IntegralMixedRoutineTaskBits.routine P q ≠ 5 := by rcases hr with hr | hr | hr <;> omega
  have hs : IntegralMixedRoutineTaskBits.routine P q = 0 ∨ IntegralMixedRoutineTaskBits.routine P q = 1 ∨
      IntegralMixedRoutineTaskBits.routine P q = 5 ∨ IntegralMixedRoutineTaskBits.routine P q = 6 := by
    rcases hr with hr | hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inr hr))
  exact (hm q hv hs).trans (model_core P a D h q h5)

theorem normalization_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedNormalizationScopedBits.CurrentMatches P a (IntegralMixedFullHistoryFamilyBits.family P D)
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.core.scalar.full) h.core.scalar.full.degree h.height h.height_binary answer := by
  intro q hs
  exact (hm q hs.1 (Or.inr (Or.inr (Or.inl hs.2.1)))).trans (model_normalization P a D h q hs.2.1)

theorem normalized_replies (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) answer := by
  intro q hv hr hp hx
  exact (normalization_matches P a D h answer hm q ⟨hv,hr,hx⟩).trans
    (IntegralMixedNormalizationScopedBits.model_phase14 P a _ _ _ _ _ q ⟨hv,hr,hx⟩ hp)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q)))
    (hr : IntegralMixedNormalizationScopedBits.RawMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedNormalizationScopedBits.correct_of_current P a _ _ _ (IntegralMixedFullHistoryFamilyBits.geometry P D)
        h.height h.height_binary h.height_bound h.modulus_bound x (normalization_matches P a D h _ hm) hr
    · intro q _
      exact IntegralMixedNormalizationScopedBits.machine_selected P a _ _ _ _ _ q
  · exact IntegralMixedFullCoreBits.correct_scoped P a D h.core x (core_matches P a D h _ hm) (normalized_replies P a D h _ hm)

end LeanCanny.Algebra.IntegralMixedNormalizedCoreBits
