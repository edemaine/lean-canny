/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Data/List/Range.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import Mathlib.Data.List.Range
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Algebraic principal subresultant identities

Adapted proof slice for the signed determinant formula used in Sturm–Tarski queries.
See STURM_SOURCES.md for the upstream source and omitted material.
-/

public section

namespace LeanCanny.Algebra.PrincipalSubresultant

open List

section

/-- The list `[f k, …, f 0]` begins with `f k`. -/
theorem map_reverse_range_succ {α : Type*} (f : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).reverse.map f = f k :: (List.range k).reverse.map f := by
  simp [List.range_succ]

/-- Mapping a function along the reversed range `[b - 1, …, 0]`, where it vanishes on
`[a, b)`, gives `b - a` zeros followed by the map along `[a - 1, …, 0]`. -/
theorem map_reverse_range_eq_replicate_append {α : Type*} [Zero α] (f : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) (h : ∀ j, a ≤ j → j < b → f j = 0) :
    (List.range b).reverse.map f = List.replicate (b - a) 0 ++ (List.range a).reverse.map f := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hlen : b + 1 - a = (b - a) + 1 := by omega
    rw [map_reverse_range_succ, h b hab (by omega), ih fun j h1 h2 => h j h1 (by omega),
      hlen, List.replicate_succ, List.cons_append]

end

end LeanCanny.Algebra.PrincipalSubresultant
