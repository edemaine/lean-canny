/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCoreCurrent
public import LeanCanny.Algebra.IntegralMixedFullEntryBoundaries
/-! # Actual row queries share the native scalar, critical, normalization, and producer core -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedArithmeticEntriesBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Controls := IntegralMixedNormalizedCoreBits.Controls

noncomputable def branch (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (IntegralMixedFullEntryBits.machine P a D h.core).withGuard (fun q => decide (IntegralMixedRoutineTaskBits.routine P q = 2))
    ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2)).flag_mem_FP
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (branch P a D h).choose (IntegralMixedNormalizedCoreBits.machine P a D h)

theorem model_entry (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 2) :
    (machine P a D h).model q = (IntegralMixedFullEntryBits.machine P a D h.core).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 2) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hr)]
  rfl

theorem model_core (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 2) :
    (machine P a D h).model q = (IntegralMixedNormalizedCoreBits.machine P a D h).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 2) then _ else _) = _
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hr)]

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (_ || (IntegralMixedNormalizedCoreBits.machine P a D h).selected q) = true
  rw [IntegralMixedNormalizedCoreBits.selected, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  by_cases hr : IntegralMixedRoutineTaskBits.routine P q = 2
  · rw [model_entry P a D h q hr]
    exact IntegralMixedFullEntryBits.canonical P a D h.core q
  · rw [model_core P a D h q hr]
    exact IntegralMixedNormalizedCoreBits.canonical P a D h q

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q →
    (IntegralMixedRoutineTaskBits.routine P q = 2 ∨ IntegralMixedRoutineTaskBits.routine P q = 0 ∨
      IntegralMixedRoutineTaskBits.routine P q = 1 ∨ IntegralMixedRoutineTaskBits.routine P q = 5 ∨
      IntegralMixedRoutineTaskBits.routine P q = 6) → answer q = (machine P a D h).model q

theorem core_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedNormalizedCoreBits.Matches P a D h answer := by
  intro q hv hr
  have h2 : IntegralMixedRoutineTaskBits.routine P q ≠ 2 := by rcases hr with hr | hr | hr | hr <;> omega
  exact (hm q hv (Or.inr hr)).trans (model_core P a D h q h2)

theorem entry_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedFullEntryBits.Matches P a D h.core answer := by
  intro q hv hr
  exact (hm q hv (Or.inl hr)).trans (model_entry P a D h q hr)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q)))
    (hr : IntegralMixedNormalizationScopedBits.RawMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedFullEntryBits.correct P a D h.core _
        (IntegralMixedNormalizedCoreBits.core_matches P a D h _ (core_matches P a D h _ hm)) (entry_matches P a D h _ hm)
    · intro q _
      exact IntegralMixedEntryDispatcherBits.selected P a _ _ q
  · exact IntegralMixedNormalizedCoreBits.correct P a D h x (core_matches P a D h _ hm) hr

end LeanCanny.Algebra.IntegralMixedArithmeticEntriesBits
