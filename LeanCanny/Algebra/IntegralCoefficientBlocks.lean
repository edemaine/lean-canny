/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPower
public import LeanCanny.Algebra.MatrixMomentPower
public import LeanCanny.Algebra.IntegralCoordinateBasisFin
public import LeanCanny.Computation.PolyTimeBinaryNat
public import Mathlib.Data.Matrix.Composition

/-! # Relative characteristic coefficients through integer matrix blocks

The characteristic polynomial is taken over the original parameter algebra.
Its coefficient multiplication matrices are obtained by mapping Berkowitz's
power construction into integer blocks. The coefficient degree remains the
relative matrix dimension; the old algebra rank affects only block size.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoefficientBlocks
open LeanCanny.Encoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {M L : ℕ}

noncomputable def blockHom (b : Module.Basis (Fin M) ℤ A) (L : ℕ) :
    Matrix (Fin L) (Fin L) A →+* Matrix (Fin (L * M)) (Fin (L * M)) ℤ :=
  (Matrix.reindexRingEquiv ℤ finProdFinEquiv).toRingHom.comp
    ((Matrix.compRingEquiv (Fin L) (Fin M) ℤ).toRingHom.comp (Algebra.leftMulMatrix b).toRingHom.mapMatrix)

theorem block_entry (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (i j : Fin L) (r t : Fin M) :
    blockHom b L T (finProdFinEquiv (i, r)) (finProdFinEquiv (j, t)) =
      Algebra.leftMulMatrix b (T i j) r t := by
  change Algebra.leftMulMatrix b
    (T ((finProdFinEquiv.symm (finProdFinEquiv (i, r))).1)
      ((finProdFinEquiv.symm (finProdFinEquiv (j, t))).1))
    ((finProdFinEquiv.symm (finProdFinEquiv (i, r))).2)
    ((finProdFinEquiv.symm (finProdFinEquiv (j, t))).2) = _
  simp only [Equiv.symm_apply_apply]

theorem block_power_entry (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (e : ℕ) (i j : Fin L) (r t : Fin M) :
    (blockHom b L T ^ e) (finProdFinEquiv (i, r)) (finProdFinEquiv (j, t)) =
      Algebra.leftMulMatrix b ((T ^ e) i j) r t := by
  rw [← map_pow, block_entry]

theorem moment_coefficient (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (row col : Fin L → A) (e : ℕ) (r t : Fin M) :
    (blockHom b (L + 2) (MatrixMoment.matrixFin row col T) ^ (e + 2))
      (finProdFinEquiv ((0 : Fin (L + 2)), r))
      (finProdFinEquiv (Fin.last (L + 1), t)) =
      Algebra.leftMulMatrix b (borderMoment row col T e) r t := by
  rw [block_power_entry, MatrixMoment.matrixFin_pow_moment]
  rfl

theorem moment_matrix_entries (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (row col : Fin L → A) (r t : Fin M) :
    (MatrixMoment.matrixFin row col T).map (fun a => Algebra.leftMulMatrix b a r t) =
      MatrixMoment.matrixFin (fun i => Algebra.leftMulMatrix b (row i) r t)
        (fun i => Algebra.leftMulMatrix b (col i) r t) (T.map (fun a => Algebra.leftMulMatrix b a r t)) := by
  ext i j
  obtain ⟨p, rfl⟩ := (MatrixMoment.vertexEquiv L).surjective i
  obtain ⟨q, rfl⟩ := (MatrixMoment.vertexEquiv L).surjective j
  rw [Matrix.map_apply, MatrixMoment.matrixFin_apply_vertex, MatrixMoment.matrixFin_apply_vertex]
  rcases p with a | (i | c) <;> rcases q with d | (j | e) <;>
    simp [MatrixMoment.matrix, MatrixMoment.withSink, MatrixMoment.sourceRow, Matrix.fromBlocks]

def dimension (L M : ℕ) : ℕ := ((L + 1) * (L + 1)) * M

theorem dimension_binary {L M : List Bool → ℕ} (hL : BinaryFn L) (hM : BinaryFn M) :
    BinaryFn (fun c => dimension (L c) (M c)) :=
  ((hL.add (BinaryFn.const 1)).mul (hL.add (BinaryFn.const 1))).mul hM

theorem characteristic_coefficient (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (d : Fin (L + 1)) (r t : Fin M) :
    (blockHom b ((L + 1) * (L + 1)) (Berkowitz.powerMatrix T) ^ L)
      (finProdFinEquiv ((Berkowitz.powerQuery L d).row, r))
      (finProdFinEquiv ((Berkowitz.powerQuery L d).col, t)) =
      Algebra.leftMulMatrix b (T.charpoly.coeff d.val) r t := by
  rw [block_power_entry, Berkowitz.powerMatrix_pow]

end LeanCanny.Algebra.IntegralCoefficientBlocks
