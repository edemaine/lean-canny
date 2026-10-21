/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDeciderFunction
public import LeanCanny.Computation.TidyBoundedFold

/-! # Bounded universal scans

A binary counter and one Boolean accumulator suffice. Each predicate query is
a native space-bounded computation, with no child transition system exposed.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedScan
open scoped Classical

def language (L : Language) (N : List Bool → ℕ) : Language :=
  {c | ∀ k < N c, pair c (BinaryNatCode.encode k) ∈ L}

noncomputable def allBelow (L : Language) (c : List Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => allBelow L c k && decide (pair c (BinaryNatCode.encode k) ∈ L)

theorem allBelow_correct (L : Language) (c : List Bool) (n : ℕ) :
    allBelow L c n = true ↔ ∀ k < n, pair c (BinaryNatCode.encode k) ∈ L := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow, Bool.and_eq_true, ih, decide_eq_true_eq]
    constructor
    · rintro ⟨h, hn⟩ k hk
      by_cases he : k = n
      · simpa [he] using hn
      · exact h k (by omega)
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

end LeanCanny.Computation.BoundedScan
