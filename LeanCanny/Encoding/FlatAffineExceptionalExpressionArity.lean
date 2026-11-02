/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalOrderedRule
public import LeanCanny.Encoding.FlatAffineExceptionalCoarseRule
public import LeanCanny.Algebra.IntegralMixedAffineCode
/-! # Every concrete exceptional affine reference names an existing bank scalar -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
open LeanCanny.Algebra IntegralMixedHistory
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineExceptionalBankSource (births)

theorem term_arity_sum (xs : List AffineExpr) (B : ℕ)
    (h : ∀ e ∈ xs, (IntegralMixedAffineCode.term e).arity ≤ B) :
    (IntegralMixedAffineCode.term (sum xs)).arity ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons e xs ih =>
    exact max_le (h e List.mem_cons_self) (ih (fun e he => h e (List.mem_cons_of_mem _ he)))

theorem term_arity_height (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) (a : Fin (arity F u) → ℤ) :
    (IntegralMixedAffineCode.term (height F u t a)).arity ≤ births F u := by
  apply term_arity_sum
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  change max 0 ((FlatAffineExceptionalParentBank.spatialIndex F u t i).val + 1) ≤ births F u
  exact max_le (Nat.zero_le _) (Nat.succ_le_of_lt (FlatAffineExceptionalParentBank.spatialIndex F u t i).isLt)

theorem term_arity_level (F : Inputs) (u : List Bool) (l : FlatAffineCriticalTower.Level (arity F u) (F.depth u) ℤ) :
    (IntegralMixedAffineCode.term (level F u l)).arity ≤ births F u := by
  cases l with
  | constant c => exact Nat.zero_le _
  | height t a => exact term_arity_height F u t a
  | midpoint l r a => exact max_le (term_arity_height F u l a) (term_arity_height F u r a)

theorem term_arity_shifted (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (j : Fin (arity F u)) :
    (IntegralMixedAffineCode.term (shifted F h u j)).arity ≤ births F u := by
  apply max_le (term_arity_level F u _)
  split_ifs
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.zero_le _

theorem ordered_heights_arity (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineExceptionalOrderedRule.frozen F u) (i : Fin (arity F u)) :
    (IntegralMixedAffineCode.term ((FlatAffineExceptionalOrderedRule.rule F h u r hr).heights i)).arity ≤ births F u :=
  term_arity_shifted F h u _

theorem coarse_heights_arity (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (arity F u)) :
    (IntegralMixedAffineCode.term ((FlatAffineExceptionalCoarseRule.rule F h u).heights i)).arity ≤ births F u :=
  term_arity_shifted F h u _
end LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
