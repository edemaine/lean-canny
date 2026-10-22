/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveStackSpace

/-! # Proof-only remaining logical transitions

No counter is added to a controller state. Its least remaining halting index
supplies the decreasing fuel used by the recursive stack theorem.
-/

@[expose] public section

namespace LeanCanny.Computation.HaltingDistance
open scoped Classical

noncomputable def remaining {S : Type} (step : S → S) (halt : S → Bool) (s : S) : ℕ :=
  if h : ∃ k, halt (step^[k] s) = true then Nat.find h else 0

theorem halts {S : Type} (step : S → S) (halt : S → Bool) (s : S)
    (h : ∃ k, halt (step^[k] s) = true) : halt (step^[remaining step halt s] s) = true := by
  simp only [remaining, dite_eq_left h]
  exact Nat.find_spec h

theorem le {S : Type} (step : S → S) (halt : S → Bool) (s : S) (k : ℕ)
    (h : halt (step^[k] s) = true) : remaining step halt s ≤ k := by
  have he : ∃ n, halt (step^[n] s) = true := ⟨k, h⟩
  simp only [remaining, dite_eq_left he]
  exact Nat.find_min' he h

theorem decreases {S : Type} (step : S → S) (halt : S → Bool) (s : S)
    (h : ∃ k, halt (step^[k] s) = true) (hn : halt s = false) :
    remaining step halt (step s) < remaining step halt s := by
  have hh := halts step halt s h
  have hp : 0 < remaining step halt s := by
    by_contra hc
    have hz : remaining step halt s = 0 := by omega
    simp only [hz, Function.iterate_zero, id_eq, hn, Bool.false_eq_true] at hh
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hh' : halt (step^[k] (step s)) = true := by
    simpa only [hk, Function.iterate_succ_apply] using hh
  have hb := le step halt (step s) k hh'
  omega

theorem suffix {S : Type} (step : S → S) (halt : S → Bool) (s : S) (n t : ℕ)
    (hn : halt (step^[n] s) = true) (ht : t ≤ n) :
    halt (step^[n - t] (step^[t] s)) = true := by
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel ht]
  exact hn

end LeanCanny.Computation.HaltingDistance
