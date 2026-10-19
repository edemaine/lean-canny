/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinaryProduct
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Complete balanced product trees

Node `i` at height `h` covers the factor interval starting at `2^h*i`.
Children have height `h-1` and indices `2*i,2*i+1`; these indices need only
as many bits as the root height. A finite factor family can be padded with ones.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct
open scoped BigOperators

def tree (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => a i
  | h + 1, i => tree a h (2 * i) * tree a h (2 * i + 1)

theorem tree_eq_prod (a : ℕ → ℕ) (h i : ℕ) :
    tree a h i = ∏ j ∈ Finset.range (2 ^ h), a (2 ^ h * i + j) := by
  induction h generalizing i with
  | zero => simp [tree]
  | succ h ih =>
    rw [tree, ih, ih, pow_succ, Nat.mul_two, Finset.prod_range_add]
    congr 1 <;> apply Finset.prod_congr rfl <;> intro j _ <;> congr 1 <;> ring

def count (k : ℕ) : ℕ := k + 1
def width (k : ℕ) : ℕ := k + 2
def limit (k : ℕ) : ℕ := k * width k + count k
def position (k t : ℕ) : ℕ := t % width k
def column (k t : ℕ) : ℕ := t / width k

structure Query where
  height : ℕ
  node : ℕ
  index : ℕ
deriving DecidableEq

def Query.left (q : Query) (t : ℕ) : Query := ⟨q.height - 1, 2 * q.node, position q.index t⟩
def Query.right (q : Query) (t : ℕ) : Query :=
  ⟨q.height - 1, 2 * q.node + 1, column q.index t - position q.index t⟩

def Query.value (a : ℕ → ℕ) (q : Query) : Bool := (tree a q.height q.node).testBit q.index
def Query.terms (a : ℕ → ℕ) (q : Query) (i : ℕ) : ℕ :=
  BinaryProduct.term (tree a (q.height - 1) (2 * q.node))
    (tree a (q.height - 1) (2 * q.node + 1)) i

def Query.carry (a : ℕ → ℕ) (q : Query) (t : ℕ) : ℕ :=
  BinarySum.carryValue (count q.index) (q.terms a) t

theorem Query.result (a : ℕ → ℕ) (q : Query) (hh : 0 < q.height) :
    decide (q.carry a (limit q.index) % 2 = 1) = q.value a := by
  have he := BinarySum.sum_testBit (count q.index) (q.terms a) q.index
  change (∑ i ∈ Finset.range (count q.index), q.terms a i).testBit q.index =
    decide (BinarySum.partialColumn (count q.index) (q.terms a) q.index (count q.index) % 2 = 1) at he
  rw [← BinarySum.carryValue_end] at he
  change decide (BinarySum.carryValue (count q.index) (q.terms a)
    (q.index * (count q.index + 1) + count q.index) % 2 = 1) = _
  rw [← he]
  rcases q with ⟨h, i, k⟩
  change 0 < h at hh
  cases h with
  | zero => omega
  | succ h =>
    simpa only [Query.terms, Query.value, tree, Nat.add_sub_cancel, count] using
      BinaryProduct.product_bit (tree a h (2 * i)) (tree a h (2 * i + 1)) k

theorem Query.term_bit (a : ℕ → ℕ) (q : Query) (t : ℕ) :
    (q.terms a (position q.index t)).testBit (column q.index t) =
      ((q.left t).value a && decide (position q.index t ≤ column q.index t) && (q.right t).value a) := by
  exact BinaryProduct.term_bit _ _ _ _

theorem column_le (k t : ℕ) (ht : t ≤ limit k) : column k t ≤ k := by
  unfold column limit width count at *
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k + 2)).mpr
  nlinarith

theorem position_le (k t : ℕ) : position k t ≤ count k := by
  have := Nat.mod_lt t (by unfold width; omega : 0 < width k)
  unfold position count width at *
  omega

end LeanCanny.Algebra.BalancedProduct
