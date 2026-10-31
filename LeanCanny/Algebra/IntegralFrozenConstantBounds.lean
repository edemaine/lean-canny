/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralFrozenCoefficientBounds
public import LeanCanny.Algebra.IntegralActionHeightBounds

/-! # Original-input heights for frozen Fermat constants and source lower parts

Retained-height powers are computed in the old multiplication matrix.
Summing frozen coordinates and scaling by the original integer leading
coefficient give a linear height budget. Adding the cleared original
polynomial bounds the actual Fermat source lower polynomial.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenConstantBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {M n dim : ℕ}

theorem add_bound (x y : ℤ) (H G : ℕ) (hx : x.natAbs ≤ 2 ^ H) (hy : y.natAbs ≤ 2 ^ G) :
    (x + y).natAbs ≤ 2 ^ (H + G + 1) := by
  have HH : 2 ^ H ≤ 2 ^ (H + G) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right H G)
  have HG : 2 ^ G ≤ 2 ^ (H + G) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left G H)
  calc
    _ ≤ x.natAbs + y.natAbs := Int.natAbs_add_le _ _
    _ ≤ 2 ^ (H + G) + 2 ^ (H + G) := Nat.add_le_add (hx.trans HH) (hy.trans HG)
    _ = _ := by rw [pow_succ]; omega

theorem subtract_bound (x y : ℤ) (H G : ℕ) (hx : x.natAbs ≤ 2 ^ H) (hy : y.natAbs ≤ 2 ^ G) :
    (x - y).natAbs ≤ 2 ^ (H + G + 1) := by
  rw [sub_eq_add_neg]
  exact add_bound x (-y) H G hx (by simpa only [Int.natAbs_neg] using hy)

def sumHeight (n M D V : ℕ) : ℕ := D * (V + M.size) + n.size

theorem sumHeight_binary {n M D V : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M) (hD : BinaryFn D) (hV : BinaryFn V) :
    BinaryFn (fun c => sumHeight (n c) (M c) (D c) (V c)) := (hD.mul (hV.add hM.size)).add hn.size

theorem frozen_height (b : Module.Basis (Fin M) ℤ A) (height : ℕ → A) (offset dim D V : ℕ)
    (hh : ∀ i : Fin n, ∀ r t, (Algebra.leftMulMatrix b (height i.val) r t).natAbs ≤ 2 ^ V) (r t : Fin M) :
    (Algebra.leftMulMatrix b (CoordinateBlockSpecialization.frozenPower (n := n) height offset dim D) r t).natAbs ≤
      2 ^ sumHeight n M D V := by
  rw [CoordinateBlockSpecialization.frozenPower, map_sum, Matrix.sum_apply]
  calc
    _ ≤ ∑ i : Fin n, (Algebra.leftMulMatrix b
        (if offset ≤ i.val ∧ i.val < offset + dim then 0 else height i.val ^ D) r t).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i : Fin n, 2 ^ (D * (V + M.size)) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
        exact Nat.zero_le _
      · rw [map_pow]
        exact IntegralParameterMatrixBounds.pow_height _ V (hh i) D r t
    _ = n * 2 ^ (D * (V + M.size)) := by simp
    _ ≤ 2 ^ n.size * 2 ^ (D * (V + M.size)) := Nat.mul_le_mul_right _ (Nat.lt_size_self n).le
    _ = _ := by rw [← pow_add, sumHeight, Nat.add_comm]

def constantHeight (n M D V C : ℕ) : ℕ := C + sumHeight n M D V

theorem constantHeight_binary {n M D V C : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M)
    (hD : BinaryFn D) (hV : BinaryFn V) (hC : BinaryFn C) :
    BinaryFn (fun c => constantHeight (n c) (M c) (D c) (V c) (C c)) :=
  hC.add (sumHeight_binary hn hM hD hV)

theorem constant_height (b : Module.Basis (Fin M) ℤ A) (height : ℕ → A) (a : ℤ) (offset dim D V C : ℕ)
    (hh : ∀ i : Fin n, ∀ r t, (Algebra.leftMulMatrix b (height i.val) r t).natAbs ≤ 2 ^ V)
    (ha : a.natAbs ≤ 2 ^ C) (m : Fin dim →₀ ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b
      ((MvPolynomial.C ((a : A) * CoordinateBlockSpecialization.frozenPower (n := n) height offset dim D) :
        MvPolynomial (Fin dim) A).coeff m) r t).natAbs ≤ 2 ^ constantHeight n M D V C := by
  rw [MvPolynomial.coeff_C]
  split_ifs
  · rw [IntegralActionHeightBounds.int_multiply_entry, Int.natAbs_mul]
    exact (Nat.mul_le_mul ha (frozen_height b height offset dim D V hh r t)).trans_eq (pow_add _ _ _).symm
  · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

def lowerHeight (n M W D C V Q P : ℕ) : ℕ :=
  IntegralFrozenCoefficientBounds.coefficientHeight n M W D C V Q + constantHeight n M D V P + 1

theorem lowerHeight_binary {n M W D C V Q P : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hC : BinaryFn C) (hV : BinaryFn V) (hQ : BinaryFn Q) (hP : BinaryFn P) :
    BinaryFn (fun c => lowerHeight (n c) (M c) (W c) (D c) (C c) (V c) (Q c) (P c)) :=
  ((IntegralFrozenCoefficientBounds.coefficientHeight_binary hn hM hW hD hC hV hQ).add
    (constantHeight_binary hn hM hD hV hP)).add (BinaryFn.const 1)

theorem lower_height (b : Module.Basis (Fin M) ℤ A) (q a : ℤ) (height : ℕ → A)
    (offset dim D W C V Q P : ℕ) (p : MvPolynomial (Fin n) A)
    (hs : ∀ e ∈ p.support, ∀ i, e i < 2 ^ W)
    (hc : ∀ e r t, (Algebra.leftMulMatrix b (p.coeff e) r t).natAbs ≤ 2 ^ C)
    (hh : ∀ i : Fin n, ∀ r t, (Algebra.leftMulMatrix b (height i.val) r t).natAbs ≤ 2 ^ V)
    (hq : q.natAbs ≤ 2 ^ Q) (ha : a.natAbs ≤ 2 ^ P) (m : Fin dim →₀ ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((ClearedCoordinateBlock.lower D (q : A) height offset dim p (a : A)).coeff m) r t).natAbs ≤
      2 ^ lowerHeight n M W D C V Q P := by
  rw [ClearedCoordinateBlock.lower, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, Matrix.add_apply]
  exact add_bound _ _ _ _ (IntegralFrozenCoefficientBounds.coefficient_height b q height offset dim D W C V Q p hs hc hh hq m r t)
    (constant_height b height a offset dim D V P hh ha m r t)

end LeanCanny.Algebra.IntegralFrozenConstantBounds
