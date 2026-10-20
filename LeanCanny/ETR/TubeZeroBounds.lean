/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeZeroSyntax

/-! # Exact arity of the sparse tube syntax

All variables fit the coordinate layout. The squared delta variable in the
radius ensures that the whole layout is covered, including for empty active
sets and sources with no point variables.
-/

@[expose] public section

namespace LeanCanny.ETR.SumSquares

theorem arity_accumulate_le (ts : List Term) (acc : Term) (A : ℕ) (ha : acc.arity ≤ A)
    (ht : ∀ t ∈ ts, t.arity ≤ A) : (accumulate ts acc).arity ≤ A := by
  induction ts generalizing acc with
  | nil => exact ha
  | cons t ts ih =>
    change (accumulate ts (.add t.square acc)).arity ≤ A
    apply ih
    · simpa only [Term.arity, Term.square, max_self] using max_le (ht t (by simp)) ha
    · intro u hu
      exact ht u (List.mem_cons_of_mem t hu)

end LeanCanny.ETR.SumSquares

namespace LeanCanny.ETR.TubeZero
open TubeEncoding

theorem arity_constraint_le (n j : ℕ) (hj : j < constraintCount n) : (constraint n j).arity ≤ dimension n := by
  unfold constraint
  have hdiv : j ≥ 2 → (j - 2) / 2 < n := by unfold constraintCount at hj; omega
  split_ifs <;> simp only [oneMinusEpsilon, Term.arity] <;> unfold dimension <;> omega

theorem arity_radius_accumulate_le (n : ℕ) :
    (SumSquares.accumulate (radiusTerms n) (.const 0)).arity ≤ dimension n := by
  apply SumSquares.arity_accumulate_le
  · exact Nat.zero_le _
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    have hj' := List.mem_range.mp hj
    change n + j + 1 ≤ dimension n
    unfold dimension
    omega

theorem arity_active_accumulate_le (n : ℕ) (bits : List Bool) :
    (SumSquares.accumulate (activeTerms n bits) (.const 0)).arity ≤ dimension n := by
  apply SumSquares.arity_accumulate_le
  · exact Nat.zero_le _
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    split_ifs
    · exact arity_constraint_le n j (List.mem_range.mp hj)
    · exact Nat.zero_le _

theorem arity_radius (n : ℕ) : (radius n).arity = dimension n := by
  have h := arity_radius_accumulate_le n
  simp only [radius, Term.square, Term.arity, max_self, zero_max]
  unfold dimension at h ⊢
  omega

theorem arity_term (n : ℕ) (bits : List Bool) : (term n bits).arity = dimension n := by
  have h := arity_active_accumulate_le n bits
  simp only [term, Term.square, Term.arity, max_self, zero_max, arity_radius]
  unfold dimension at h ⊢
  omega

end LeanCanny.ETR.TubeZero
