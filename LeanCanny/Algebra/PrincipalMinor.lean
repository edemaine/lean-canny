/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Minor
public import LeanCanny.Algebra.SubresultantMinor

/-! # Principal-minor embeddings including terminal orders

The retained row at principal order k is k+i. The two column blocks skip k
columns, just as for interior subresultants. Non-strict order bounds cover the
terminal one-block minor and the empty equal-degree minor.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalMinor

def row (m n k : ℕ) (hm : k ≤ m) (hn : k ≤ n)
    (i : Fin ((m - k) + (n - k))) : Fin (m + n) := ⟨k + i.val, by omega⟩

def col (m n k : ℕ) (hm : k ≤ m) (hn : k ≤ n)
    (j : Fin ((m - k) + (n - k))) : Fin (m + n) :=
  ⟨Subresultant.colIndex m k j.val, by unfold Subresultant.colIndex; split_ifs <;> omega⟩

theorem minor_eq_submatrix {R : Type*} [Semiring R] (p q : Polynomial R) (m n k : ℕ)
    (hm : k ≤ m) (hn : k ≤ n) :
    Subresultant.minor p q m n k k = (Polynomial.sylvester p q m n).submatrix
      (row m n k hm hn) (col m n k hm hn) := by
  funext i j
  rw [Subresultant.minor_apply, Matrix.submatrix_apply, SylvesterBits.sylvester_apply]
  have hr : Subresultant.rowIndex k k i.val = k + i.val := by
    unfold Subresultant.rowIndex
    split_ifs <;> omega
  simp only [row, col, hr]
  by_cases hj : j.val < m - k
  · have hjm : j.val < m := by omega
    simp only [Subresultant.colIndex, ite_eq_left hj, hjm, ↓reduceIte, Subresultant.band]
  · have hjm : ¬j.val + k < m := by omega
    have hs : j.val + k - m = j.val - (m - k) := by omega
    simp only [Subresultant.colIndex, ite_eq_right hj, hjm, ↓reduceIte, hs, Subresultant.band]

end LeanCanny.Algebra.PrincipalMinor
