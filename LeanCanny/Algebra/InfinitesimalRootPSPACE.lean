/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalRootCountSpace

/-! # Eventual algebraic-root sign realizability is in PSPACE

For a nonzero symbolic root polynomial, the computed count is positive exactly
when every sufficiently small positive beta admits a real root with the desired
signs. The unguarded language assumes nonzero symbolic roots on all inputs; the
guarded language includes this condition in its semantics.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalRootBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open DyadicSignPatternBits

def Realizes (F : Family) (c : List Bool) (beta : ℝ) : Prop := ∃ a : ℝ,
  ((F.root.polynomial c).map (ParameterTarski.evalHom beta)).eval a = 0 ∧
    ∀ i : Fin (Nat.fromBitsLE (F.count c)),
      SignType.sign (((queries F c i).map (ParameterTarski.evalHom beta)).eval a) = pattern F c i

theorem positive_iff_reference (F : Family) (c : List Bool) (hp : F.root.polynomial c ≠ 0) :
    c ∈ positiveLanguage F ↔ Realizes F c (reference F c) := by
  have hn := ParameterTarski.map_ne_zero_on_interval (F.root.polynomial c) hp (queries F c)
    (reference F c) (InfinitesimalSign.dyadic_pos _) le_rfl
  exact RootSignQueries.root_signCount_pos _ hn _ _

theorem realizes_iff_positive (F : Family) (c : List Bool) (hp : F.root.polynomial c ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (hbr : beta ≤ reference F c) :
    Realizes F c beta ↔ c ∈ positiveLanguage F := by
  have he := ParameterTarski.realizable_stable (F.root.polynomial c) hp (queries F c) (pattern F c)
    beta (reference F c) hb (InfinitesimalSign.dyadic_pos _) hbr le_rfl
  exact he.trans (positive_iff_reference F c hp).symm

def eventualRealizableLanguage (F : Family) : Language := {c | ∃ delta : ℝ, 0 < delta ∧
  ∀ beta : ℝ, 0 < beta → beta < delta → Realizes F c beta}

def guardedRealizableLanguage (F : Family) : Language :=
  {c | F.root.polynomial c ≠ 0 ∧ c ∈ eventualRealizableLanguage F}

theorem eventual_iff_positive (F : Family) (c : List Bool) (hp : F.root.polynomial c ≠ 0) :
    c ∈ eventualRealizableLanguage F ↔ c ∈ positiveLanguage F := by
  constructor
  · rintro ⟨delta, hd, he⟩
    let beta := min (delta / 2) (reference F c)
    have hb : 0 < beta := lt_min (half_pos hd) (InfinitesimalSign.dyadic_pos _)
    have hbd : beta < delta := (min_le_left _ _).trans_lt (half_lt_self hd)
    exact (realizes_iff_positive F c hp beta hb (min_le_right _ _)).mp (he beta hb hbd)
  · intro h
    refine ⟨reference F c, InfinitesimalSign.dyadic_pos _, ?_⟩
    intro beta hb hbr
    exact (realizes_iff_positive F c hp beta hb hbr.le).mpr h

theorem eventualRootCount_zero (F : Family) (c : List Bool) (hp : F.root.polynomial c = 0) :
    eventualRootCount F c = 0 := by
  simp only [eventualRootCount, hp, Polynomial.map_zero, Polynomial.roots_zero, Multiset.toFinset_zero,
    RootSignQueries.signCount, Finset.filter_empty, Finset.card_empty]

theorem positiveLanguage_eq_guarded (F : Family) : positiveLanguage F = guardedRealizableLanguage F := by
  ext c
  by_cases hp : F.root.polynomial c = 0
  · simp only [positiveLanguage, guardedRealizableLanguage, Set.mem_ofPred_eq,
      eventualRootCount_zero F c hp, lt_self_iff_false, hp, ne_eq, not_true_eq_false, false_and]
  · change c ∈ positiveLanguage F ↔ F.root.polynomial c ≠ 0 ∧ c ∈ eventualRealizableLanguage F
    exact ⟨fun h => ⟨hp, (eventual_iff_positive F c hp).mpr h⟩,
      fun h => (eventual_iff_positive F c hp).mp h.2⟩

theorem guardedRealizableLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    guardedRealizableLanguage F ∈ PSPACE := by
  rw [← positiveLanguage_eq_guarded]
  exact positiveLanguage_mem_PSPACE a hF hs H P

theorem eventualRealizableLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient)
    (hp : ∀ c, F.root.polynomial c ≠ 0) : eventualRealizableLanguage F ∈ PSPACE := by
  have he : guardedRealizableLanguage F = eventualRealizableLanguage F := by
    ext c
    change (F.root.polynomial c ≠ 0 ∧ c ∈ eventualRealizableLanguage F) ↔ c ∈ eventualRealizableLanguage F
    exact ⟨fun h => h.2, fun h => ⟨hp c, h⟩⟩
  rw [← he]
  exact guardedRealizableLanguage_mem_PSPACE a hF hs H P

end LeanCanny.Algebra.InfinitesimalRootBits
