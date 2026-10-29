/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatCriticalTower
public import LeanCanny.Algebra.TriangularPolynomialRows

/-! # Explicit critical and copy rows of the indexed flat tower

Each critical row uses only its own complete ambient variable block. Each
copy row subtracts the same spatial coordinate in the immediately preceding
block, with zero at the first stage. These are exactly the existing indexed
tower equations, not a separately assumed polynomial family.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatCriticalIndexedRows
open MvPolynomial TriangularPolynomialRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def previousPolynomial (j k : ℕ) (h : j < k) (i : Fin n) : MvPolynomial (Fin (k * n)) R :=
  if j = 0 then 0 else X (block n (j - 1) k (by omega) i)

theorem rename_previous (j k : ℕ) (h : j < k) (i : Fin n) :
    rename (embedding n j k h) (FlatCriticalStage.oldCoordinate (FlatCriticalTower.previous n j i)) =
      (previousPolynomial j k h i : MvPolynomial (Fin (k * n)) R) := by
  cases j with
  | zero => simp [FlatCriticalTower.previous, FlatCriticalStage.oldCoordinate, previousPolynomial]
  | succ j =>
    simpa [FlatCriticalTower.previous, FlatCriticalStage.oldCoordinate, previousPolynomial] using
      congrArg (fun a : Fin (k * n) => (X a : MvPolynomial (Fin (k * n)) R))
        (embedding_previous n j k h i)

noncomputable def row (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) (j k : ℕ) (h : j < k) (i : Fin n) :
    MvPolynomial (Fin (k * n)) R :=
  if i ∈ s j then rename (block n j k h) (ProjectionCriticalFamily.spatialEquation p (base j) (v j) i)
  else X (block n j k h i) - previousPolynomial j k h i

theorem system_row (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
    (base : ℕ → Fin n) (v : ℕ → Fin n → R) (j k : ℕ) (h : j < k) (i : Fin n) :
    FlatCriticalTower.system p s base v k (block n j k h i) = row p s base v j k h i := by
  rw [FlatCriticalTower.system, stage_row]
  change rename (embedding n j k h) (FlatCriticalStage.row p (s j) (base j) (v j)
    (FlatCriticalTower.previous n j) i) = _
  by_cases hi : i ∈ s j
  · simp only [FlatCriticalStage.row, row, hi, ite_true, rename_rename]
    apply congrArg (fun f : Fin n → Fin (k * n) => rename f (ProjectionCriticalFamily.spatialEquation p (base j) (v j) i))
    exact funext (embedding_current n j k h)
  · simp only [FlatCriticalStage.row, row, hi, ite_false, map_sub, rename_X,
      embedding_current]
    rw [rename_previous (R := R) j k h i]

end LeanCanny.Algebra.FlatCriticalIndexedRows
