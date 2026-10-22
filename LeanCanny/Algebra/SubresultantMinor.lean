/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Subresultant
public import LeanCanny.Algebra.SylvesterAccessCorrect

/-!
# Embedding a subresultant minor in the full Sylvester matrix

Column indices skip the `k` removed columns at the end of the first block.
Rows select the requested low coefficient and the retained high coefficients.
The index formulas use only comparison, addition, and truncated subtraction,
making them suitable for uniform binary access.
-/

@[expose] public section

namespace LeanCanny.Algebra.Subresultant

def colIndex (m k j : ℕ) : ℕ := if j < m - k then j else j + k

theorem rowIndex_lt (m n k r i : ℕ) (hm : k < m) (hn : k < n) (hr : r ≤ k)
    (hi : i < (m - k) + (n - k)) : rowIndex k r i < m + n := by
  unfold rowIndex
  split_ifs <;> omega

theorem colIndex_lt (m n k j : ℕ) (hm : k < m) (hn : k < n)
    (hj : j < (m - k) + (n - k)) : colIndex m k j < m + n := by
  unfold colIndex
  split_ifs <;> omega

theorem minor_apply {R : Type*} [Semiring R] (f g : Polynomial R) (m n k r : ℕ)
    (i j : Fin ((m - k) + (n - k))) :
    minor f g m n k r i j =
      if j.val < m - k then band g n (rowIndex k r i.val) j.val
      else band f m (rowIndex k r i.val) (j.val - (m - k)) := by
  induction j using Fin.addCases <;> simp [minor, Fin.addCases_left, Fin.addCases_right]

def rowEmbedding (m n k r : ℕ) (hm : k < m) (hn : k < n) (hr : r ≤ k)
    (i : Fin ((m - k) + (n - k))) : Fin (m + n) :=
  ⟨rowIndex k r i.val, rowIndex_lt m n k r i.val hm hn hr i.is_lt⟩

def colEmbedding (m n k : ℕ) (hm : k < m) (hn : k < n)
    (j : Fin ((m - k) + (n - k))) : Fin (m + n) :=
  ⟨colIndex m k j.val, colIndex_lt m n k j.val hm hn j.is_lt⟩

theorem minor_eq_submatrix {R : Type*} [Semiring R] (f g : Polynomial R) (m n k r : ℕ)
    (hm : k < m) (hn : k < n) (hr : r ≤ k) :
    minor f g m n k r = (Polynomial.sylvester f g m n).submatrix
      (rowEmbedding m n k r hm hn hr) (colEmbedding m n k hm hn) := by
  funext i j
  rw [minor_apply, Matrix.submatrix_apply, SylvesterBits.sylvester_apply]
  simp only [rowEmbedding, colEmbedding]
  by_cases hj : j.val < m - k
  · have hjm : j.val < m := by omega
    simp only [colIndex, ite_eq_left hj, hjm, ↓reduceIte, band]
  · have hjm : ¬ j.val + k < m := by omega
    have hs : j.val + k - m = j.val - (m - k) := by omega
    simp only [colIndex, ite_eq_right hj, hjm, ↓reduceIte, hs, band]

theorem rowEmbedding_injective (m n k r : ℕ) (hm : k < m) (hn : k < n) (hr : r ≤ k) :
    Function.Injective (rowEmbedding m n k r hm hn hr) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp only [rowEmbedding, rowIndex] at h
  split_ifs at h <;> omega

theorem colEmbedding_injective (m n k : ℕ) (hm : k < m) (hn : k < n) :
    Function.Injective (colEmbedding m n k hm hn) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp only [colEmbedding, colIndex] at h
  split_ifs at h <;> omega

end LeanCanny.Algebra.Subresultant
