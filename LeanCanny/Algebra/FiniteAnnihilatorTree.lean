/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedPrimitiveVectors

/-! # Balanced primitive parameters for arbitrary finite integer annihilator families

Nonzero inputs are made square-free once, then padded with X. Each padded leaf
has exactly the root zero, so padding preserves the original Cartesian product.
The height is the binary size of the family count, including count zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorTree
open Polynomial BalancedPrimitiveTree
open scoped BigOperators

noncomputable def padding : SeparableIntegerPolynomial := ⟨X, by simpa only [Polynomial.map_X] using (separable_X (R := ℚ))⟩

noncomputable def leaf (p : ℕ → ℤ[X]) (n : ℕ) (hp : ∀ i < n, p i ≠ 0) (i : ℕ) : SeparableIntegerPolynomial :=
  if hi : i < n then SeparableIntegerPolynomial.squarefree (p i) (hp i hi) else padding

variable (p : ℕ → ℤ[X]) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)

noncomputable def parameter : SeparableIntegerPolynomial := node (leaf p n hp) n.size 0

theorem width_bound (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have hs : 1 ≤ n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have hl : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    have h := Nat.mul_le_mul_right 2 hl
    rw [← pow_succ, Nat.sub_add_cancel hs] at h
    omega

theorem leaf_degree (i : ℕ) (hi : i < n) :
    (leaf p n hp i).polynomial.natDegree = (ScaledSquarefree.polynomial (p i)).natDegree := by
  rw [leaf, dite_eq_left hi]
  rfl

theorem padding_degree (i : ℕ) (hi : n ≤ i) : (leaf p n hp i).polynomial.natDegree = 1 := by
  rw [leaf, dite_eq_right (by omega)]
  exact natDegree_X

theorem parameter_degree :
    (parameter p n hp).polynomial.natDegree = ∏ i ∈ Finset.range n, (ScaledSquarefree.polynomial (p i)).natDegree := by
  have hn : n ≤ 2 ^ n.size := (Nat.lt_size_self n).le
  rw [parameter, degree_eq_prod]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [← Nat.add_sub_of_le hn, Finset.prod_range_add]
  have ht : ∏ j ∈ Finset.range (2 ^ n.size - n), (leaf p n hp (n + j)).polynomial.natDegree = 1 := by
    apply Finset.prod_eq_one
    intro j _
    exact padding_degree p n hp (n + j) (by omega)
  rw [ht, mul_one]
  apply Finset.prod_congr rfl
  intro i hi
  exact leaf_degree p n hp i (Finset.mem_range.mp hi)

theorem parameter_degree_le (D : ℕ) (hD : ∀ i < n, (p i).natDegree ≤ D) :
    (parameter p n hp).polynomial.natDegree ≤ D ^ n := by
  rw [parameter_degree]
  calc
    _ ≤ ∏ _i ∈ Finset.range n, D := Finset.prod_le_prod (fun i hi =>
      (ScaledSquarefree.polynomial_natDegree_le (p i) (hp i (Finset.mem_range.mp hi))).trans (hD i (Finset.mem_range.mp hi)))
    _ = _ := by simp

variable {L : Type*} [Field L] [CharZero L]

theorem leaf_root (i : ℕ) (hi : i < n) (x : L) :
    (leaf p n hp i).polynomial.eval₂ (Int.castRingHom L) x = 0 ↔ (p i).eval₂ (Int.castRingHom L) x = 0 := by
  rw [leaf, dite_eq_left hi]
  exact ScaledSquarefree.roots_iff (p i) (hp i hi) x

omit [CharZero L] in
theorem padding_root (i : ℕ) (hi : n ≤ i) (x : L) :
    (leaf p n hp i).polynomial.eval₂ (Int.castRingHom L) x = 0 ↔ x = 0 := by
  rw [leaf, dite_eq_right (by omega)]
  simp only [padding, Polynomial.eval₂_X]

noncomputable def decode (theta : L) : Fin n → L := fun i =>
  coordinate n.size (BalancedPrimitiveTree.decode (leaf p n hp) n.size 0 theta) i.val

theorem decode_root (theta : L) (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom L) theta = 0) (i : Fin n) :
    (p i.val).eval₂ (Int.castRingHom L) (decode p n hp theta i) = 0 := by
  have hr := decode_coordinate (leaf p n hp) n.size 0 theta ht i.val (i.isLt.trans (Nat.lt_size_self n))
  simp only [Nat.mul_zero, Nat.zero_add] at hr
  exact (leaf_root p n hp i.val i.isLt _).mp hr

end LeanCanny.Algebra.FiniteAnnihilatorTree
