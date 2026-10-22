/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveGramEliminant
public import LeanCanny.Algebra.MacaulayRoots

/-! # The full Macaulay matrix with fixed-width row and column boxes

Every raw shift is a row; incompatible shifts give zero rows. Identity rows
on the columns outside the homogeneous level complete the column box.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBox
open scoped Classical Matrix BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]
abbrev Column (n W : ℕ) := Macaulay.Index n W
abbrev Row (n W : ℕ) := Sum (Fin n × Column n W) (Column n W)

noncomputable def matrix (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) : Matrix (Row n W) (Column n W) R
  | .inl (i, a), b => if (FixedWidthPolynomial.vector n W a).degree + d i = Macaulay.level d then
      (monomial (FixedWidthPolynomial.vector n W a) 1 * p i).coeff
        (FixedWidthPolynomial.vector n W b) else 0
  | .inr a, b => if (FixedWidthPolynomial.vector n W a).degree ≠ Macaulay.level d then
      if a = b then 1 else 0 else 0

lemma matrix_map {S : Type*} [CommRing S] (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (phi : R →+* S) :
    (matrix p d W).map phi = matrix (fun i => (p i).map phi) d W := by
  funext a b
  rcases a with ⟨i, a⟩ | a
  · change phi (if _ then _ else 0) = if _ then _ else 0
    split_ifs with h
    · rw [← MvPolynomial.coeff_map]
      simp only [map_mul, MvPolynomial.map_monomial, map_one]
    · exact map_zero phi
  · change phi (if _ then (if _ then 1 else 0) else 0) = if _ then (if _ then 1 else 0) else 0
    split_ifs <;> first | exact map_zero phi | exact map_one phi

lemma sourceRow_apply (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (a : Macaulay.MultiplierIndex d W) (b : Column n W) :
    matrix p d W (.inl (a.1, a.2.val)) b =
      (Macaulay.sourceRow p d W a).coeff (FixedWidthPolynomial.vector n W b) := by
  rw [matrix, ite_eq_left ((Macaulay.mem_multiplierIndices d W a.1 a.2.val).mp a.2.property)]
  rfl

private lemma sum_active (d : Fin n → ℕ) (W : ℕ) (f : Column n W → R)
    (hf : ∀ b, (FixedWidthPolynomial.vector n W b).degree ≠ Macaulay.level d → f b = 0) :
    (∑ b, f b) = ∑ b : Macaulay.activeIndices d W, f b.val := by
  rw [Finset.sum_coe_sort]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro b _ hb
  exact hf b (fun h => hb ((Macaulay.mem_activeIndices d W b).mpr h))

lemma mulVec_sourceRow (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (a : Macaulay.MultiplierIndex d W) (v : Column n W → R) :
    (matrix p d W *ᵥ v) (.inl (a.1, a.2.val)) =
      (Macaulay.fullMatrix p d W *ᵥ fun b => v b.val) a := by
  change (∑ b, _ * v b) = ∑ b : Macaulay.activeIndices d W, _ * v b.val
  simp_rw [sourceRow_apply]
  apply sum_active
  intro b hb
  rw [(Macaulay.sourceRow_homogeneous p d W hp a).coeff_eq_zero hb, zero_mul]

lemma mulVec_padding (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (v : Column n W → R) (a : Column n W)
    (ha : (FixedWidthPolynomial.vector n W a).degree ≠ Macaulay.level d) :
    (matrix p d W *ᵥ v) (.inr a) = v a := by
  change (∑ b, _ * v b) = v a
  simp [matrix, ha]

lemma mulVec_injective_of_fullMatrix_surjective (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hA : Function.Surjective (Macaulay.fullMatrix p d W).vecMul) :
    Function.Injective (matrix p d W).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp hA
  have hi : Function.Injective (Macaulay.fullMatrix p d W).mulVec := by
    intro x y h
    have H := congrArg B.mulVec h
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using H
  intro x y h
  have he : (fun b : Macaulay.activeIndices d W => x b.val) = fun b => y b.val := by
    apply hi
    funext a
    simpa only [mulVec_sourceRow p d W hp] using congrFun h (.inl (a.1, a.2.val))
  funext a
  by_cases ha : (FixedWidthPolynomial.vector n W a).degree = Macaulay.level d
  · exact congrFun he ⟨a, (Macaulay.mem_activeIndices d W a).mpr ha⟩
  · simpa only [mulVec_padding p d W x a ha, mulVec_padding p d W y a ha] using congrFun h (.inr a)

lemma mulVec_evaluation_eq_zero (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hW : Macaulay.level d < 2 ^ W) (x : Fin n → R)
    (hx : ∀ i, MvPolynomial.eval x (p i) = 0) :
    matrix p d W *ᵥ Macaulay.evaluationVector d W x = 0 := by
  funext a
  rcases a with ⟨i, a⟩ | a
  · by_cases ha : (FixedWidthPolynomial.vector n W a).degree + d i = Macaulay.level d
    · let a' : Macaulay.MultiplierIndex d W := ⟨i, a, (Macaulay.mem_multiplierIndices d W i a).mpr ha⟩
      have hh := Macaulay.sourceRow_homogeneous p d W hp a'
      change (∑ b : Column n W, matrix p d W _ b * Macaulay.evaluationVector d W x b) = 0
      calc
        _ = ∑ b : Column n W, (Macaulay.sourceRow p d W a').coeff (FixedWidthPolynomial.vector n W b) *
            MvPolynomial.eval x (monomial (FixedWidthPolynomial.vector n W b) 1) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [show matrix p d W (.inl (i, a)) b = _ from sourceRow_apply p d W a' b]
          by_cases hb : (FixedWidthPolynomial.vector n W b).degree = Macaulay.level d
          · rw [Macaulay.evaluationVector, ite_eq_left hb]
          · rw [Macaulay.evaluationVector, ite_eq_right hb, hh.coeff_eq_zero hb]
            simp
        _ = MvPolynomial.eval x (Macaulay.sourceRow p d W a') :=
          (Macaulay.eval_fixedWidth _ _ W hh.totalDegree_le hW x).symm
        _ = 0 := by simp [Macaulay.sourceRow, map_mul, hx]
    · change (∑ b : Column n W, matrix p d W _ b * Macaulay.evaluationVector d W x b) = 0
      simp [matrix, ha]
  · by_cases ha : (FixedWidthPolynomial.vector n W a).degree = Macaulay.level d
    · change (∑ b : Column n W, matrix p d W _ b * Macaulay.evaluationVector d W x b) = 0
      simp [matrix, ha]
    · rw [mulVec_padding p d W _ a ha]
      exact ite_eq_right ha

lemma source_entry (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (i : Fin n) (a b : Column n W) :
    matrix p d W (.inl (i, a)) b =
      if (FixedWidthPolynomial.vector n W a).degree + d i = Macaulay.level d ∧
          FixedWidthPolynomial.vector n W a ≤ FixedWidthPolynomial.vector n W b then
        (p i).coeff (FixedWidthPolynomial.vector n W b - FixedWidthPolynomial.vector n W a)
      else 0 := by
  rw [matrix, MvPolynomial.coeff_monomial_mul']
  split_ifs <;> simp_all

lemma entry_cases (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (a : Row n W) (b : Column n W) :
    matrix p d W a b = 0 ∨ matrix p d W a b = 1 ∨
      ∃ i e, matrix p d W a b = (p i).coeff e := by
  rcases a with ⟨i, a⟩ | a
  · rw [source_entry]
    split_ifs
    · exact Or.inr (Or.inr ⟨i, _, rfl⟩)
    · exact Or.inl rfl
  · simp only [matrix]
    split_ifs <;> simp

lemma card_column (n W : ℕ) : Fintype.card (Column n W) = FixedWidthPolynomial.count n W := by
  simp [Column, Macaulay.Index]

lemma card_row (n W : ℕ) : Fintype.card (Row n W) = (n + 1) * FixedWidthPolynomial.count n W := by
  simp [Row, Column, Macaulay.Index, Nat.add_mul]

end LeanCanny.Algebra.MacaulayFullBox
