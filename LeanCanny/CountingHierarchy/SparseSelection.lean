/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Lean.Elab.Tactic.Omega

/-!
# Selecting one object with logarithmically many equality tests

A family of labels separating the members of a finite set admits a short
list of tests selecting one member. The bound is expressed as `card ≤ 2^N`,
so clients do not need a convention for the logarithm of an empty set.
-/

public section

namespace LeanCanny.CountingHierarchy

open scoped Classical

variable {α ι β : Type*}

/-- All the recorded label values agree at the object. -/
@[expose] def matchesTests (f : ι → α → β) (L : List (ι × β)) (x : α) : Prop :=
  ∀ c ∈ L, f c.1 x = c.2

/-- Repeatedly keep a smallest nonempty label class. Each step halves
 the remaining candidates and adds one ordinary equality test. -/
theorem exists_sparse_selector (f : ι → α → β) (N : ℕ) (S : Finset α)
    (hS : S.Nonempty) (hcard : S.card ≤ 2 ^ N)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, f i x ≠ f i y) :
    ∃ L : List (ι × β), L.length ≤ N ∧
      ∃ x ∈ S, ∀ y ∈ S, matchesTests f L y ↔ y = x := by
  induction N generalizing S with
  | zero =>
    obtain ⟨x, hx⟩ := hS
    refine ⟨[], by simp, x, hx, ?_⟩
    intro y hy
    have heq : y = x := Finset.card_le_one.mp (by simpa using hcard) y hy x hx
    simp [matchesTests, heq]
  | succ N ih =>
    obtain ⟨a, ha⟩ := hS
    by_cases hsingle : ∀ b ∈ S, b = a
    · refine ⟨[], by simp, a, ha, ?_⟩
      intro y hy
      simp [matchesTests, hsingle y hy]
    · obtain ⟨b, hb, hba⟩ : ∃ b ∈ S, b ≠ a := by
        simpa only [not_forall, not_imp, exists_prop] using hsingle
      obtain ⟨i, hi⟩ := hsep a ha b hb (Ne.symm hba)
      let Sa := S.filter (fun x => f i x = f i a)
      let Sb := S.filter (fun x => f i x = f i b)
      have hSa : Sa.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
      have hSb : Sb.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, rfl⟩⟩
      have hdisj : Disjoint Sa Sb := by
        apply Finset.disjoint_left.mpr
        intro x hxa hxb
        exact hi ((Finset.mem_filter.mp hxa).2.symm.trans (Finset.mem_filter.mp hxb).2)
      have hsum : Sa.card + Sb.card ≤ S.card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      obtain ⟨v, hv, hvcard⟩ : ∃ v : β,
          (S.filter (fun x => f i x = v)).Nonempty ∧
          2 * (S.filter (fun x => f i x = v)).card ≤ S.card := by
        by_cases hh : 2 * Sa.card ≤ S.card
        · exact ⟨f i a, hSa, hh⟩
        · exact ⟨f i b, hSb, by change 2 * Sb.card ≤ S.card; omega⟩
      let T := S.filter (fun x => f i x = v)
      have hT : T.card ≤ 2 ^ N := by
        rw [pow_succ] at hcard
        change 2 * T.card ≤ S.card at hvcard
        omega
      have hTsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ j, f j x ≠ f j y := by
        intro x hx y hy hxy
        exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
      obtain ⟨L, hL, x, hx, hsel⟩ := ih T hv hT hTsep
      refine ⟨(i, v) :: L, by simpa using Nat.succ_le_succ hL,
        x, (Finset.mem_filter.mp hx).1, ?_⟩
      intro y hy
      constructor
      · intro hm
        have hyi : f i y = v := hm (i, v) (by simp)
        have hyT : y ∈ T := Finset.mem_filter.mpr ⟨hy, hyi⟩
        apply (hsel y hyT).mp
        intro c hc
        exact hm c (List.mem_cons_of_mem _ hc)
      · intro hyx
        subst y
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact (Finset.mem_filter.mp hx).2
        · exact (hsel x hx).mpr rfl c hc

end LeanCanny.CountingHierarchy
