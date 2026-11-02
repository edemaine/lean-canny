/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedEntry
public import LeanCanny.Algebra.IntegralMixedGramScopedCurrent
public import LeanCanny.Algebra.IntegralMixedPscContextBranch
/-! # Framed determinant arithmetic closes over actual routine-two entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable abbrev family := IntegralMixedFramedEntryBits.family
noncomputable abbrev input := IntegralMixedFramedEntryBits.input
abbrev Controls := IntegralMixedFramedEntryBits.Controls

noncomputable def psc (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  IntegralMixedPscContextBranchBits.branch P a (family P D H) (input P a D H h)
noncomputable def gram (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  IntegralMixedGramScopedBits.machine P a (family P D H) (input P a D H h)
noncomputable def machine (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  (psc P a D H h).choose (gram P a D H h)

attribute [local irreducible] psc gram
private theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = if M.selected q then M.model q else N.model q := rfl
private theorem choose_selected (M N : Machine) (q : List Bool) :
    (M.choose N).selected q = (M.selected q || N.selected q) := rfl

theorem model_psc (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hq : IntegralMixedPscContextBranchBits.InScope P (family P D H) q) :
    (machine P a D H h).model q = (psc P a D H h).model q := by
  have HS : (psc P a D H h).selected q = true := by
    unfold psc
    exact (IntegralMixedPscContextBranchBits.branch_selected P a _ _ q).mpr hq
  simp only [machine, choose_model, HS, ite_true]

theorem model_gram (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hq : IntegralMixedGramScopedBits.InScope P q) :
    (machine P a D H h).model q = (gram P a D H h).model q := by
  have HP : 19 ≤ phase q := by
    have HE := hq.2
    unfold IntegralMixedGramScopedBits.PhaseAllowed at HE
    omega
  have HS : (psc P a D H h).selected q = false := by
    unfold psc
    exact IntegralMixedPscContextBranchBits.branch_not_gram P a _ _ q HP
  simp only [machine, choose_model, HS, Bool.false_eq_true, ite_false]

theorem selected (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    (machine P a D H h).selected q = true := by
  have HS : (gram P a D H h).selected q = true := by
    unfold gram
    exact IntegralMixedGramScopedBits.machine_selected P a _ _ q
  simp only [machine, choose_selected, HS, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D H h).model q := by
  rw [machine, choose_model]
  split_ifs
  · unfold psc
    exact IntegralMixedPscContextBranchBits.canonical P a _ _ q
  · unfold gram
    exact IntegralMixedGramScopedBits.canonical P a _ _ q

abbrev Matches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 →
    answer q = (machine P a D H h).model q

theorem psc_matches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedPscContextBranchBits.CurrentMatches P a (family P D H) (input P a D H h) answer := by
  intro q hq
  have HE := (hm q hq.1.1 hq.1.2.1).trans (model_psc P a D H h q hq)
  simpa only [psc] using HE

theorem gram_matches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedGramScopedBits.CurrentMatches P a (family P D H) (input P a D H h) answer := by
  intro q hq
  have HE := (hm q hq.1.1 hq.1.2.1).trans (model_gram P a D H h q hq)
  simpa only [gram] using HE

theorem correct (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (x : (q : List Bool) → ZMod (modulus P q))
    (he : IntegralMixedFramedEntryBits.Matches P a D H h (fun q => residueBits (x q)))
    (hm : Matches P a D H h (fun q => residueBits (x q))) :
    Correct (machine P a D H h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · unfold psc
    apply IntegralMixedPscContextBranchBits.correct_of_current P a _ _
      (IntegralMixedFramedHistoryFamilyBits.geometry P D H) x
    · intro q hq
      exact IntegralMixedEntryDispatcherBits.psc_matches_all P a _ _ _ he q hq
    · exact psc_matches P a D H h _ hm
  · unfold gram
    exact IntegralMixedGramScopedBits.correct_of_entries P a _ _
      (IntegralMixedFramedHistoryFamilyBits.geometry P D H) x he (gram_matches P a D H h _ hm)

end LeanCanny.Algebra.IntegralMixedFramedDeterminantBits
