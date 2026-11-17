/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SparseSelection
public import LeanCanny.Algebra.ThomEncoding

/-! # Selecting one real root by a short list of derivative signs -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped Classical

/-- The full Thom signature can be replaced by at most `N` derivative
 tests when selecting some member of a nonempty root set of size at most `2^N`.
 All derivative indices are between one and `D`; the zeroth derivative is
 omitted because it vanishes at every candidate root. -/
theorem exists_sparse_root_selector (p : ℝ[X]) (hp : p ≠ 0) (D N : ℕ)
    (hD : p.natDegree ≤ D) (S : Finset ℝ) (hS : S.Nonempty)
    (hroot : ∀ x ∈ S, p.eval x = 0) (hcard : S.card ≤ 2 ^ N) :
    ∃ L : List (Fin D × SignType), L.length ≤ N ∧
      ∃ x ∈ S, ∀ y ∈ S,
        matchesTests (fun i : Fin D => fun z => LeanCanny.Algebra.ThomEncoding.sign p z (i.val + 1)) L y ↔
          y = x := by
  apply exists_sparse_selector _ N S hS hcard
  intro x hx y hy hxy
  by_contra h
  have hall (i : Fin D) : LeanCanny.Algebra.ThomEncoding.sign p x (i.val + 1) =
      LeanCanny.Algebra.ThomEncoding.sign p y (i.val + 1) := by
    by_contra hne
    exact h ⟨i, hne⟩
  apply hxy
  apply LeanCanny.Algebra.ThomEncoding.root_eq p hp D hD x y (hroot x hx) (hroot y hy)
  intro k hk
  cases k with
  | zero => simp [LeanCanny.Algebra.ThomEncoding.sign, hroot x hx, hroot y hy]
  | succ k => exact hall ⟨k, by omega⟩

/-- The usual root-count bound supplies the cardinality hypothesis for
 any chosen subset of the real roots. -/
theorem exists_sparse_root_selector_of_degree (p : ℝ[X]) (hp : p ≠ 0) (D N : ℕ)
    (hD : p.natDegree ≤ D) (hDN : D ≤ 2 ^ N) (S : Finset ℝ) (hS : S.Nonempty)
    (hroot : ∀ x ∈ S, p.eval x = 0) :
    ∃ L : List (Fin D × SignType), L.length ≤ N ∧
      ∃ x ∈ S, ∀ y ∈ S,
        matchesTests (fun i : Fin D => fun z => LeanCanny.Algebra.ThomEncoding.sign p z (i.val + 1)) L y ↔
          y = x := by
  apply exists_sparse_root_selector p hp D N hD S hS hroot
  have hsub : S.val ⊆ p.roots := by
    intro x hx
    exact (Polynomial.mem_roots hp).mpr (hroot x hx)
  exact (Polynomial.card_le_degree_of_subset_roots hsub).trans (hD.trans hDN)

/-- In the quartic reduction the critical-value degree is at most `5^n`,
 so `3n` derivative tests suffice, with binary derivative indices. -/
theorem exists_sparse_root_selector_five (p : ℝ[X]) (hp : p ≠ 0) (n : ℕ)
    (hD : p.natDegree ≤ 5 ^ n) (S : Finset ℝ) (hS : S.Nonempty)
    (hroot : ∀ x ∈ S, p.eval x = 0) :
    ∃ L : List (Fin (5 ^ n) × SignType), L.length ≤ 3 * n ∧
      ∃ x ∈ S, ∀ y ∈ S,
        matchesTests (fun i : Fin (5 ^ n) => fun z =>
          LeanCanny.Algebra.ThomEncoding.sign p z (i.val + 1)) L y ↔ y = x := by
  apply exists_sparse_root_selector_of_degree p hp (5 ^ n) (3 * n) hD _ S hS hroot
  calc
    5 ^ n ≤ (2 ^ 3) ^ n := Nat.pow_le_pow_left (by decide) n
    _ = 2 ^ (3 * n) := (pow_mul 2 3 n).symm

end LeanCanny.CountingHierarchy
