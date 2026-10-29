/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TriangularPolynomialIndexing
public import LeanCanny.Algebra.BlockRenameCoefficient

/-! # Indexed row semantics for arbitrary flat polynomial towers

The row at stage j and spatial index i is the original stage row renamed into
the prefix of the complete variable layout. Appending stages preserves all
earlier row and variable indices.
-/

@[expose] public section
namespace LeanCanny.Algebra.TriangularPolynomialRows
open MvPolynomial TriangularPolynomialTower TriangularPolynomialIndexing
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def prefixIndex (n a b : ℕ) (h : a ≤ b) : Fin (a * n) → Fin (b * n) :=
  Fin.castLE (Nat.mul_le_mul_right n h)

def block (n j k : ℕ) (h : j < k) : Fin n → Fin (k * n) :=
  BlockRenameCoefficient.shift n (k * n) (j * n)
    (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n h)

def embedding (n j k : ℕ) (h : j < k) : Variables n (j + 1) → Fin (k * n) :=
  prefixIndex n (j + 1) k h ∘ enumerate n (j + 1)

theorem embedding_current (n j k : ℕ) (h : j < k) (i : Fin n) :
    embedding n j k h (Sum.inr i) = block n j k h i := by
  apply Fin.ext
  exact enumerate_new n j i

theorem embedding_previous (n j k : ℕ) (h : j + 1 < k) (i : Fin n) :
    embedding n (j + 1) k h (Sum.inl (Sum.inr i)) = block n j k (by omega) i := by
  apply Fin.ext
  change (enumerate n (j + 2) (Sum.inl (Sum.inr i))).val = j * n + i.val
  rw [enumerate_old, enumerate_new]

variable {n : ℕ} {R : Type*} [CommRing R]

theorem at_enumerate (F : Family n R) (k : ℕ) (v : Variables n k) :
    TriangularPolynomialIndexing.system F k (enumerate n k v) =
      rename (enumerate n k) (TriangularPolynomialTower.system F k v) := by
  simp only [TriangularPolynomialIndexing.system, PolynomialSystemReindex.system, Equiv.symm_apply_apply]

theorem old_row (F : Family n R) (k : ℕ) (i : Fin (k * n)) :
    TriangularPolynomialIndexing.system F (k + 1) (prefixIndex n k (k + 1) (by omega) i) =
      rename (prefixIndex n k (k + 1) (by omega)) (TriangularPolynomialIndexing.system F k i) := by
  let v := (enumerate n k).symm i
  have hv : enumerate n k v = i := (enumerate n k).apply_symm_apply i
  have hi : prefixIndex n k (k + 1) (by omega) i = enumerate n (k + 1) (Sum.inl v) := by
    apply Fin.ext
    rw [enumerate_old, hv]
    rfl
  rw [hi, at_enumerate, ← hv, at_enumerate]
  change rename (enumerate n (k + 1)) (rename Sum.inl (TriangularPolynomialTower.system F k v)) = _
  rw [rename_rename, rename_rename]
  apply congrArg (fun f : Variables n k → Fin ((k + 1) * n) => rename f (TriangularPolynomialTower.system F k v))
  funext x
  apply Fin.ext
  exact enumerate_old n k x

theorem stage_row (F : Family n R) (k j : ℕ) (hj : j < k) (i : Fin n) :
    TriangularPolynomialIndexing.system F k (block n j k hj i) =
      rename (embedding n j k hj) (F.row j i) := by
  induction k generalizing j i with
  | zero => omega
  | succ k ih =>
    by_cases he : j = k
    · subst j
      have hr : block n k (k + 1) hj i = enumerate n (k + 1) (Sum.inr i) := by
        apply Fin.ext
        exact (enumerate_new n k i).symm
      rw [hr, at_enumerate]
      change rename (enumerate n (k + 1)) (F.row k i) = _
      apply congrArg (fun f : Variables n (k + 1) → Fin ((k + 1) * n) => rename f (F.row k i))
      funext x
      exact Fin.ext rfl
    · have hprev : j < k := by omega
      have hr : block n j (k + 1) hj i = prefixIndex n k (k + 1) (by omega) (block n j k hprev i) := Fin.ext rfl
      rw [hr, old_row, ih j hprev i, rename_rename]
      apply congrArg (fun f : Variables n (j + 1) → Fin ((k + 1) * n) => rename f (F.row j i))
      funext x
      exact Fin.ext rfl

end LeanCanny.Algebra.TriangularPolynomialRows
