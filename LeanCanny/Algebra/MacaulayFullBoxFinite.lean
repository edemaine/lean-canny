/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveBoxGramEliminant

/-! # Numeric indices for the fixed Macaulay block determinant

The first n*C slots are source rows in quotient/remainder order, the next
C are inactive-column padding, and the last C are Gram columns.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBoxFinite
open scoped Classical Matrix
set_option backward.isDefEq.respectTransparency false
variable {n W : ℕ} {R : Type*} [CommRing R]

abbrev count (n W : ℕ) := FixedWidthPolynomial.count n W

def rowEquiv (n W : ℕ) : MacaulayFullBox.Row n W ≃ Fin ((n + 1) * count n W) :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by ring))

def blockEquiv (n W : ℕ) :
    Sum (MacaulayFullBox.Row n W) (MacaulayFullBox.Column n W) ≃ Fin ((n + 2) * count n W) :=
  ((Equiv.sumCongr (rowEquiv n W) (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by ring))

lemma source_code (i : Fin n) (a : MacaulayFullBox.Column n W) :
    (blockEquiv n W (.inl (.inl (i, a)))).val = i.val * count n W + a.val := by
  simp [blockEquiv, rowEquiv, finSumFinEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

lemma padding_code (a : MacaulayFullBox.Column n W) :
    (blockEquiv n W (.inl (.inr a))).val = n * count n W + a.val := by
  simp [blockEquiv, rowEquiv, finSumFinEquiv, Nat.add_comm]

lemma column_code (a : MacaulayFullBox.Column n W) :
    (blockEquiv n W (.inr a)).val = (n + 1) * count n W + a.val := by
  simp [blockEquiv, finSumFinEquiv, Nat.add_comm]

/-- The source pair is decoded by natural quotient and remainder. -/
lemma source_decode (r : Fin ((n + 2) * count n W)) (hr : r.val < n * count n W) :
    (blockEquiv n W).symm r = .inl (.inl (finProdFinEquiv.symm ⟨r.val, hr⟩)) := by
  apply (blockEquiv n W).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [source_code]
  change r.val = (r.val / count n W) * count n W + r.val % count n W
  simpa only [Nat.mul_comm] using (Nat.div_add_mod r.val (count n W)).symm

lemma padding_decode (r : Fin ((n + 2) * count n W))
    (hl : n * count n W ≤ r.val) (hr : r.val < (n + 1) * count n W) :
    (blockEquiv n W).symm r = .inl (.inr ⟨r.val - n * count n W, by
      change r.val - n * count n W < count n W
      have h : (n + 1) * count n W = n * count n W + count n W := by ring
      omega⟩) := by
  apply (blockEquiv n W).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [padding_code]
  change r.val = n * count n W + (r.val - n * count n W)
  omega

lemma column_decode (r : Fin ((n + 2) * count n W))
    (hl : (n + 1) * count n W ≤ r.val) :
    (blockEquiv n W).symm r = .inr ⟨r.val - (n + 1) * count n W, by
      change r.val - (n + 1) * count n W < count n W
      have h : (n + 2) * count n W = (n + 1) * count n W + count n W := by ring
      have := r.isLt
      omega⟩ := by
  apply (blockEquiv n W).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [column_code]
  change r.val = (n + 1) * count n W + (r.val - (n + 1) * count n W)
  omega

noncomputable def matrix (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Matrix (Fin ((n + 2) * count n W)) (Fin ((n + 2) * count n W)) R :=
  (ProjectiveGramEliminant.block (MacaulayFullBox.matrix p d W)).submatrix
    (blockEquiv n W).symm (blockEquiv n W).symm

lemma det_matrix (p : Fin n → MvPolynomial (Fin n) ProjectiveBoxGramEliminant.Coefficient)
    (d : Fin n → ℕ) (W : ℕ) :
    (matrix p d W).det = ProjectiveBoxGramEliminant.polynomial p d W := by
  rw [matrix, Matrix.det_submatrix_equiv_self, ProjectiveBoxGramEliminant.block_det]

lemma matrix_entry_property (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (P : R → Prop) (h0 : P 0) (h1 : P 1) (hn : ∀ a, P a → P (-a))
    (hp : ∀ i e, P ((p i).coeff e)) (a b : Fin ((n + 2) * count n W)) :
    P (matrix p d W a b) := by
  have hA : ∀ a b, P (MacaulayFullBox.matrix p d W a b) := by
    intro a b
    rcases MacaulayFullBox.entry_cases p d W a b with hz | ho | ⟨i, e, he⟩
    · rw [hz]; exact h0
    · rw [ho]; exact h1
    · rw [he]; exact hp i e
  change P (ProjectiveGramEliminant.block (MacaulayFullBox.matrix p d W)
    ((blockEquiv n W).symm a) ((blockEquiv n W).symm b))
  generalize (blockEquiv n W).symm a = a'
  generalize (blockEquiv n W).symm b = b'
  rcases a' with a' | a' <;> rcases b' with b' | b'
  · change P ((1 : Matrix (MacaulayFullBox.Row n W) (MacaulayFullBox.Row n W) R) a' b')
    by_cases h : a' = b'
    · simpa only [Matrix.one_apply, ite_eq_left h] using h1
    · simpa only [Matrix.one_apply, ite_eq_right h] using h0
  · exact hA a' b'
  · exact hn _ (hA b' a')
  · exact h0

lemma matrix_inner_degree (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial R)))
    (d : Fin n → ℕ) (W D : ℕ) (hp : ∀ i e k, (((p i).coeff e).coeff k).natDegree ≤ D)
    (a b : Fin ((n + 2) * count n W)) (k : ℕ) :
    ((matrix p d W a b).coeff k).natDegree ≤ D :=
  matrix_entry_property p d W (fun a => (a.coeff k).natDegree ≤ D)
    (by simp) (by simp only [Polynomial.coeff_one]; split_ifs <;> simp)
    (fun a ha => by simpa only [Polynomial.coeff_neg, Polynomial.natDegree_neg] using ha)
    (fun i e => hp i e k) a b

end LeanCanny.Algebra.MacaulayFullBoxFinite
