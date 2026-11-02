/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullGramArithmetic
public import LeanCanny.Algebra.IntegralMixedPscContextBranch
/-! # Disjoint same-context PSC and Gram determinant arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev family := IntegralMixedFullEntryBits.family
noncomputable abbrev input := IntegralMixedFullEntryBits.input
abbrev Controls := IntegralMixedFullCoreBits.Controls

noncomputable def psc (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedPscContextBranchBits.branch P a (family P D) (input P a D h)
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (psc P a D h).choose (IntegralMixedFullGramBits.machine P a D h)

theorem model_psc (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hq : IntegralMixedPscContextBranchBits.InScope P (family P D) q) :
    (machine P a D h).model q = (psc P a D h).model q := by
  change (if (psc P a D h).selected q then _ else _) = _
  have HS : (psc P a D h).selected q = true :=
    (IntegralMixedPscContextBranchBits.branch_selected P a (family P D) (input P a D h) q).mpr hq
  exact ite_eq_left HS

theorem model_gram (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hq : IntegralMixedGramScopedBits.InScope P q) :
    (machine P a D h).model q = (IntegralMixedFullGramBits.machine P a D h).model q := by
  have HP : 19 ≤ phase q := by
    have H := hq.2
    unfold IntegralMixedGramScopedBits.PhaseAllowed at H
    omega
  change (if (psc P a D h).selected q then _ else _) = _
  rw [show (psc P a D h).selected q = false from IntegralMixedPscContextBranchBits.branch_not_gram P a _ _ q HP]
  rfl

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (_ || (IntegralMixedFullGramBits.machine P a D h).selected q) = true
  rw [IntegralMixedGramScopedBits.machine_selected, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z = if (psc P a D h).selected q then _ else _
  split_ifs
  · exact IntegralMixedPscContextBranchBits.canonical P a _ _ q
  · exact IntegralMixedFullGramBits.canonical P a D h q

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 → answer q = (machine P a D h).model q

theorem psc_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedPscContextBranchBits.CurrentMatches P a (family P D) (input P a D h) answer := by
  intro q hq
  exact (hm q hq.1.1 hq.1.2.1).trans (model_psc P a D h q hq)

theorem gram_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedFullGramBits.Matches P a D h answer := by
  intro q hq
  exact (hm q hq.1.1 hq.1.2.1).trans (model_gram P a D h q hq)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q))
    (he : IntegralMixedFullEntryBits.Matches P a D h (fun q => residueBits (x q)))
    (hm : Matches P a D h (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply IntegralMixedPscContextBranchBits.correct_of_current P a _ _ (IntegralMixedFullHistoryFamilyBits.geometry P D) x
    · intro q hq
      exact IntegralMixedEntryDispatcherBits.psc_matches_all P a _ _ _ he q hq
    · exact psc_matches P a D h _ hm
  · exact IntegralMixedFullGramBits.correct P a D h x he (gram_matches P a D h _ hm)

end LeanCanny.Algebra.IntegralMixedFullDeterminantBits
