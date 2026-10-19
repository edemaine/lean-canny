/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzCoefficients
public import LeanCanny.Algebra.MatrixPowerControllerCorrect

/-!
# A scalar matrix moment as one power entry

A source, the original matrix vertices, and a sink form an augmented matrix.
The source edges carry r, the sink edges carry c, and the interior edges carry
A. The source-to-sink entry of its `(k+2)`nd power is `r A^k c`.
Only two vertices are added. Reindexing places source at zero, interior i at
i+1, and sink last, allowing direct binary entry access.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.MatrixMoment
open Matrix

variable {R : Type*} [Semiring R] {n : ℕ}

def withSink (A : Matrix (Fin n) (Fin n) R) (c : Fin n → R) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
  fromBlocks A (replicateCol Unit c) (0 : Matrix Unit (Fin n) R) 0

theorem withSink_pow (A : Matrix (Fin n) (Fin n) R) (c : Fin n → R) (k : ℕ) :
    withSink A c ^ (k + 1) =
      fromBlocks (A ^ (k + 1)) (A ^ k * replicateCol Unit c) (0 : Matrix Unit (Fin n) R) 0 := by
  induction k with
  | zero => simp [withSink]
  | succ k ih =>
      rw [pow_succ, ih, withSink, fromBlocks_multiply]
      simp [Matrix.mul_assoc, pow_succ]

theorem withSource_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix Unit ι R) (D : Matrix ι ι R) (k : ℕ) :
    (fromBlocks (0 : Matrix Unit Unit R) B (0 : Matrix ι Unit R) D) ^ (k + 1) =
      fromBlocks 0 (B * D ^ k) (0 : Matrix ι Unit R) (D ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, fromBlocks_multiply]
      simp [Matrix.mul_assoc, pow_succ]

def sourceRow (r : Fin n → R) : Matrix Unit (Fin n ⊕ Unit) R :=
  fun _ q => Sum.elim r (fun _ => 0) q

def matrix (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Unit ⊕ (Fin n ⊕ Unit)) (Unit ⊕ (Fin n ⊕ Unit)) R :=
  fromBlocks (0 : Matrix Unit Unit R)
    (sourceRow r)
    (0 : Matrix (Fin n ⊕ Unit) Unit R) (withSink A c)

theorem matrix_pow_moment (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    (matrix r c A ^ (k + 2)) (.inl ()) (.inr (.inr ())) = r ⬝ᵥ (A ^ k *ᵥ c) := by
  unfold matrix
  rw [show k + 2 = (k + 1) + 1 by omega, withSource_pow, withSink_pow]
  simp [sourceRow, Matrix.mul_apply, Fintype.sum_sum_type, dotProduct, mulVec]

def vertexEquiv (n : ℕ) : Unit ⊕ (Fin n ⊕ Unit) ≃ Fin (n + 2) :=
  (Equiv.sumCongr (Equiv.refl Unit)
    ((Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv.symm).trans finSumFinEquiv)).trans
      (Berkowitz.headTailEquiv (n + 1))

@[simp] theorem vertexEquiv_source (n : ℕ) : vertexEquiv n (.inl ()) = 0 := rfl

@[simp] theorem vertexEquiv_middle (i : Fin n) :
    vertexEquiv n (.inr (.inl i)) = i.castSucc.succ := rfl

@[simp] theorem vertexEquiv_sink (n : ℕ) :
    vertexEquiv n (.inr (.inr ())) = Fin.last (n + 1) := by
  apply Fin.ext
  simp [vertexEquiv, Berkowitz.headTailEquiv, finOneEquiv]

def matrixFin (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  Matrix.reindexRingEquiv R (vertexEquiv n) (matrix r c A)

theorem matrixFin_apply_vertex (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (p q : Unit ⊕ (Fin n ⊕ Unit)) :
    matrixFin r c A (vertexEquiv n p) (vertexEquiv n q) = matrix r c A p q := by
  simp [matrixFin, Matrix.reindex_apply]

theorem matrixFin_pow_moment (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    (matrixFin r c A ^ (k + 2)) 0 (Fin.last (n + 1)) = r ⬝ᵥ (A ^ k *ᵥ c) := by
  rw [← vertexEquiv_source n, ← vertexEquiv_sink n]
  unfold matrixFin
  rw [← map_pow]
  simpa only [Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using matrix_pow_moment r c A k

theorem run_moment (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    (MatrixPower.step (matrixFin r c A))^[MatrixPower.work (n + 2) (k + 2).size (k + 2) + 1]
      (.eval ⟨(k + 2).size, k + 2, 0, Fin.last (n + 1)⟩ []) = .done (r ⬝ᵥ (A ^ k *ᵥ c)) := by
  rw [MatrixPower.run_pow, matrixFin_pow_moment]

theorem run_moment_residue_length (m : ℕ) [NeZero m] (r c : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (k t : ℕ) :
    (MatrixPower.stateBits MatrixPower.residueBits ((MatrixPower.step (matrixFin r c A))^[t]
      (.eval ⟨(k + 2).size, k + 2, 0, Fin.last (n + 1)⟩ []))).length ≤
        64 * ((n + 2).size + (k + 2).size + m.size + 1) ^ 2 :=
  MatrixPower.run_residueBits_quadratic m (matrixFin r c A) (k + 2) t _ _

end LeanCanny.Algebra.MatrixMoment
