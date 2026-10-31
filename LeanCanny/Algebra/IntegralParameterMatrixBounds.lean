/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterExtensionMatrix
public import LeanCanny.Algebra.CharacteristicIntegerBounds

/-! # Entry-height bounds for scalar parameter multiplication matrices

The new rank is the old rank times the selected degree. Its generator's
entry-height exponent is at most degree times the old exponent plus the
binary size of the old rank. The bound permits binary degrees and ranks.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterMatrixBounds
open Matrix
open scoped Classical BigOperators

theorem mul_height {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) (H G : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ G) (i j : Fin n) :
    ((A * B) i j).natAbs ≤ 2 ^ (H + G + n.size) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin n, (A i k * B k j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : Fin n, 2 ^ H * 2 ^ G := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hA i k) (hB k j)
    _ = n * (2 ^ H * 2 ^ G) := by simp
    _ ≤ 2 ^ n.size * (2 ^ H * 2 ^ G) :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self n).le
    _ = 2 ^ (H + G + n.size) := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem pow_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) (e : ℕ) (i j : Fin n) :
    ((A ^ e) i j).natAbs ≤ 2 ^ (e * (H + n.size)) := by
  induction e generalizing i j with
  | zero =>
    simp only [pow_zero, Nat.zero_mul, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ e ih =>
    rw [pow_succ']
    have Hmul := mul_height A (A ^ e) H (e * (H + n.size)) hA (fun i j => ih i j) i j
    convert Hmul using 1
    congr 1
    ring

def height (n d H : ℕ) : ℕ := d * (H + n.size)

theorem height_binary {n d H : List Bool → ℕ} (hn : BinaryFn n) (hd : BinaryFn d) (hH : BinaryFn H) :
    BinaryFn (fun c => height (n c) (d c) (H c)) := hd.mul (hH.add hn.size)

theorem normalized_height {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) (H d k : ℕ) (hk : k < d)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ H) (i j : Fin n) :
    ((A * B ^ (d - 1 - k)) i j).natAbs ≤ 2 ^ height n d H := by
  have HM := mul_height A (B ^ (d - 1 - k)) H ((d - 1 - k) * (H + n.size)) hA
    (fun i j => pow_height B H hB _ i j) i j
  apply HM.trans
  apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
  calc
    _ = (d - 1 - k + 1) * (H + n.size) := by ring
    _ ≤ d * (H + n.size) := Nat.mul_le_mul_right _ (by omega)

theorem root_height {A : Type*} [CommRing A] [Nontrivial A] {n d : ℕ}
    (b : Module.Basis (Fin n) ℤ A) (p : Polynomial A) (H : ℕ)
    (hp : ∀ k i j, (Algebra.leftMulMatrix b (p.coeff k) i j).natAbs ≤ 2 ^ H)
    (i j : Fin n × Fin d) :
    (Algebra.leftMulMatrix (IntegralParameterExtension.basis b p d)
      (AdjoinRoot.root _) i j).natAbs ≤ 2 ^ height n d H := by
  rw [IntegralParameterExtension.basis_root_matrix_of_coefficients]
  split_ifs
  · simp only [Int.natAbs_one]
    exact Nat.one_le_two_pow
  · simp only [Int.natAbs_zero]
    exact Nat.zero_le _
  · simp only [Int.natAbs_zero]
    exact Nat.zero_le _
  · rw [Int.natAbs_neg]
    exact normalized_height _ _ H d i.2.val i.2.isLt (hp i.2.val) (hp d) i.1 j.1

end LeanCanny.Algebra.IntegralParameterMatrixBounds
