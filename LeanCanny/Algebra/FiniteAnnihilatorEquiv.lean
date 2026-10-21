/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorTree

/-! # Root bijections for arbitrary finite annihilator families

The finite vector interface removes the auxiliary padded coordinates. It
includes the empty family, whose parameter is X and whose solution vector
is unique. Coordinates are recovered by nested rational pair formulas.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorTree
open Polynomial BalancedPrimitiveTree

def extend {L : Type*} (n : ℕ) (x : Fin n → L) [Zero L] (j : ℕ) : L :=
  if hj : j < n then x ⟨j, hj⟩ else 0

def preparedValues {L : Type*} [Zero L] (n : ℕ) (x : Fin n → L) : Values L n.size := tabulate n.size (extend n x)

variable (p : ℕ → ℤ[X]) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
variable {L : Type*} [Field L] [CharZero L]

theorem prepared_valid (x : Fin n → L) (hx : ∀ i, (p i.val).eval₂ (Int.castRingHom L) (x i) = 0) :
    valid (leaf p n hp) n.size 0 (preparedValues n x) := by
  apply (valid_iff _ _ _ _).mpr
  intro j hj
  simp only [Nat.mul_zero, Nat.zero_add, preparedValues, coordinate_tabulate _ _ _ hj]
  by_cases hjn : j < n
  · apply (leaf_root p n hp j hjn _).mpr
    simpa only [extend, dite_eq_left hjn] using hx ⟨j, hjn⟩
  · apply (padding_root p n hp j (by omega) _).mpr
    simp only [extend, dite_eq_right hjn]

noncomputable def encode (x : Fin n → L) : L :=
  BalancedPrimitiveTree.encode (leaf p n hp) n.size 0 (preparedValues n x)

theorem encode_root (x : Fin n → L) (hx : ∀ i, (p i.val).eval₂ (Int.castRingHom L) (x i) = 0) :
    (parameter p n hp).polynomial.eval₂ (Int.castRingHom L) (encode p n hp x) = 0 :=
  (encode_valid (leaf p n hp) n.size 0 (preparedValues n x) (prepared_valid p n hp x hx)).1

theorem decode_encode (x : Fin n → L) (hx : ∀ i, (p i.val).eval₂ (Int.castRingHom L) (x i) = 0) :
    decode p n hp (encode p n hp x) = x := by
  have he := (encode_valid (leaf p n hp) n.size 0 (preparedValues n x) (prepared_valid p n hp x hx)).2
  funext i
  change coordinate n.size (BalancedPrimitiveTree.decode (leaf p n hp) n.size 0
    (BalancedPrimitiveTree.encode (leaf p n hp) n.size 0 (preparedValues n x))) i.val = x i
  rw [he, preparedValues, coordinate_tabulate _ _ _ (i.isLt.trans (Nat.lt_size_self n))]
  simp only [extend, dite_eq_left i.isLt]

theorem encode_decode (theta : L) (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom L) theta = 0) :
    encode p n hp (decode p n hp theta) = theta := by
  have hr := BalancedPrimitiveTree.decode_root (leaf p n hp) n.size 0 theta ht
  have hv := (valid_iff (leaf p n hp) n.size 0 _).mp hr.1
  have he : preparedValues n (decode p n hp theta) = BalancedPrimitiveTree.decode (leaf p n hp) n.size 0 theta := by
    apply coordinate_injective
    intro j hj
    rw [preparedValues, coordinate_tabulate _ _ _ hj]
    by_cases hjn : j < n
    · rw [extend, dite_eq_left hjn]
      rfl
    · rw [extend, dite_eq_right hjn]
      have hjzero := (padding_root p n hp j (by omega) _).mp (by
        simpa only [Nat.mul_zero, Nat.zero_add] using hv j hj)
      exact hjzero.symm
  change BalancedPrimitiveTree.encode (leaf p n hp) n.size 0 _ = theta
  rw [he]
  exact hr.2

noncomputable def rootEquiv :
    {theta : L // (parameter p n hp).polynomial.eval₂ (Int.castRingHom L) theta = 0} ≃
      {x : Fin n → L // ∀ i, (p i.val).eval₂ (Int.castRingHom L) (x i) = 0} where
  toFun theta := ⟨decode p n hp theta.val, decode_root p n hp theta.val theta.property⟩
  invFun x := ⟨encode p n hp x.val, encode_root p n hp x.val x.property⟩
  left_inv theta := Subtype.ext (encode_decode p n hp theta.val theta.property)
  right_inv x := Subtype.ext (decode_encode p n hp x.val x.property)

theorem parameter_empty (p : ℕ → ℤ[X]) (hp : ∀ i < 0, p i ≠ 0) : (parameter p 0 hp).polynomial = X := rfl

end LeanCanny.Algebra.FiniteAnnihilatorTree
