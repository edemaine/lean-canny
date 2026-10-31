/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterMatrixBounds
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Relative characteristic heights linear in the original entry height

All bounds concern old multiplication-matrix entries of actual algebra
products and determinants. The outer matrix dimension and old rank stay
separate. Only binary sizes of the old rank enter the height exponent.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeCharacteristicBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {M : ℕ}

theorem list_product_height (b : Module.Basis (Fin M) ℤ A) (l : List A) (H : ℕ)
    (h : ∀ x ∈ l, ∀ r t, (Algebra.leftMulMatrix b x r t).natAbs ≤ 2 ^ H) :
    ∀ r t, (Algebra.leftMulMatrix b l.prod r t).natAbs ≤ 2 ^ (l.length * (H + M.size)) := by
  revert h
  induction l with
  | nil =>
    intro _ r t
    simp only [List.prod_nil, map_one, Matrix.one_apply, List.length_nil, Nat.zero_mul, pow_zero]
    split_ifs <;> norm_num
  | cons x xs ih =>
    intro h r t
    have HX := h x List.mem_cons_self
    have HT : ∀ y ∈ xs, ∀ r t, (Algebra.leftMulMatrix b y r t).natAbs ≤ 2 ^ H :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons, map_mul, List.length_cons]
    have HP := IntegralParameterMatrixBounds.mul_height (Algebra.leftMulMatrix b x)
      (Algebra.leftMulMatrix b xs.prod) H (xs.length * (H + M.size)) HX (ih HT) r t
    convert HP using 1
    congr 1
    ring

theorem finset_product_height {ι : Type*} (b : Module.Basis (Fin M) ℤ A) (s : Finset ι) (f : ι → A) (H : ℕ)
    (h : ∀ i ∈ s, ∀ r t, (Algebra.leftMulMatrix b (f i) r t).natAbs ≤ 2 ^ H) (r t : Fin M) :
    (Algebra.leftMulMatrix b (∏ i ∈ s, f i) r t).natAbs ≤ 2 ^ (s.card * (H + M.size)) := by
  have HP := list_product_height b (s.toList.map f) H (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact h i (Finset.mem_toList.mp hi)) r t
  simpa only [Finset.prod_map_toList, List.length_map, Finset.length_toList] using HP

theorem unit_smul_entry_abs (b : Module.Basis (Fin M) ℤ A) (u : ℤˣ) (x : A) (r t : Fin M) :
    (Algebra.leftMulMatrix b (u • x) r t).natAbs = (Algebra.leftMulMatrix b x r t).natAbs := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [one_smul]
  · simp [Units.smul_def]

def determinantHeight (n M H : ℕ) : ℕ := n * (H + M.size + n.size)

theorem determinantHeight_binary {n M H : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M) (hH : BinaryFn H) :
    BinaryFn (fun c => determinantHeight (n c) (M c) (H c)) := hn.mul ((hH.add hM.size).add hn.size)

theorem determinantHeight_mono {n N : ℕ} (h : n ≤ N) (M H : ℕ) :
    determinantHeight n M H ≤ determinantHeight N M H :=
  Nat.mul_le_mul h (Nat.add_le_add_left (Nat.size_le_size h) _)

theorem determinant_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis (Fin M) ℤ A) (T : Matrix ι ι A) (H : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H) (r t : Fin M) :
    (Algebra.leftMulMatrix b T.det r t).natAbs ≤ 2 ^ determinantHeight (Fintype.card ι) M H := by
  rw [Matrix.det_apply, map_sum, Matrix.sum_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, (Algebra.leftMulMatrix b (Equiv.Perm.sign σ • ∏ i, T (σ i) i) r t).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, (Algebra.leftMulMatrix b (∏ i, T (σ i) i) r t).natAbs := by
      simp only [unit_smul_entry_abs]
    _ ≤ ∑ _σ : Equiv.Perm ι, 2 ^ (Fintype.card ι * (H + M.size)) := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Finset.card_univ] using finset_product_height b Finset.univ (fun i => T (σ i) i) H
        (fun i _ => h (σ i) i) r t
    _ = (Fintype.card ι).factorial * 2 ^ (Fintype.card ι * (H + M.size)) := by simp [Fintype.card_perm]
    _ ≤ (Fintype.card ι) ^ (Fintype.card ι) * 2 ^ (Fintype.card ι * (H + M.size)) :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ ≤ (2 ^ (Fintype.card ι).size) ^ (Fintype.card ι) * 2 ^ (Fintype.card ι * (H + M.size)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      congr 1
      unfold determinantHeight
      ring

def characteristicHeight (n M H : ℕ) : ℕ := determinantHeight n M H + n

theorem characteristicHeight_binary {n M H : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M) (hH : BinaryFn H) :
    BinaryFn (fun c => characteristicHeight (n c) (M c) (H c)) :=
  (determinantHeight_binary hn hM hH).add hn

theorem characteristicHeight_linear (n M H : ℕ) :
    characteristicHeight n M H = n * H + n * (M.size + n.size + 1) := by
  unfold characteristicHeight determinantHeight
  ring

theorem characteristicHeight_linear_bound (n M H : ℕ) :
    characteristicHeight n M H ≤ n * (M.size + n.size + 1) * (H + 1) := by
  have HB : 1 ≤ M.size + n.size + 1 := by omega
  have HN : n ≤ n * (M.size + n.size + 1) := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n HB
  rw [characteristicHeight_linear]
  calc
    _ ≤ n * (M.size + n.size + 1) * H + n * (M.size + n.size + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right H HN) _
    _ = _ := by ring

theorem neg_one_pow_entry_abs (b : Module.Basis (Fin M) ℤ A) (k : ℕ) (x : A) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((-1 : A) ^ k * x) r t).natAbs = (Algebra.leftMulMatrix b x r t).natAbs := by
  induction k with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', neg_one_mul, neg_mul, map_neg, Matrix.neg_apply, Int.natAbs_neg]
    exact ih

theorem minors_height {L : ℕ} (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A) (d H : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H) (r t : Fin M) :
    (Algebra.leftMulMatrix b (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard d,
      (T.submatrix (Subtype.val : s → Fin L) (Subtype.val : s → Fin L)).det) r t).natAbs ≤
        2 ^ characteristicHeight L M H := by
  have HC : ((Finset.univ : Finset (Fin L)).powersetCard d).card ≤ 2 ^ L := by
    calc
      _ ≤ ((Finset.univ : Finset (Fin L)).powerset).card := Finset.card_le_card (by
        intro s hs
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hs).1)
      _ = _ := by simp
  rw [map_sum, Matrix.sum_apply]
  calc
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard d,
        (Algebra.leftMulMatrix b (T.submatrix (Subtype.val : s → Fin L) (Subtype.val : s → Fin L)).det r t).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin L)).powersetCard d, 2 ^ determinantHeight L M H := by
      apply Finset.sum_le_sum
      intro s _
      have HS : s.card ≤ L := by
        simpa only [Finset.card_univ, Fintype.card_fin] using (Finset.card_le_card (Finset.subset_univ s))
      have HD := determinant_height b (T.submatrix (Subtype.val : s → Fin L) (Subtype.val : s → Fin L)) H
        (fun i j => h i.val j.val) r t
      simp only [Fintype.card_coe] at HD
      exact HD.trans (Nat.pow_le_pow_right (by decide) (determinantHeight_mono HS M H))
    _ = ((Finset.univ : Finset (Fin L)).powersetCard d).card * 2 ^ determinantHeight L M H := by simp
    _ ≤ 2 ^ L * 2 ^ determinantHeight L M H := Nat.mul_le_mul_right _ HC
    _ = _ := by rw [← pow_add, characteristicHeight, Nat.add_comm]

theorem coefficient_height [Nontrivial A] {L : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (T : Matrix (Fin L) (Fin L) A) (H : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H) (k : ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b (T.charpoly.coeff k) r t).natAbs ≤ 2 ^ characteristicHeight L M H := by
  by_cases hk : k ≤ L
  · have HE : L - (L - k) = k := Nat.sub_sub_self hk
    have HC := Matrix.charpoly_coeff_eq_sum_minors T (L - k) (by simpa only [Fintype.card_fin] using Nat.sub_le L k)
    simp only [Fintype.card_fin, HE] at HC
    rw [HC, neg_one_pow_entry_abs]
    exact minors_height b T (L - k) H h r t
  · have HD : T.charpoly.natDegree < k := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt HD, map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

end LeanCanny.Algebra.IntegralRelativeCharacteristicBounds
