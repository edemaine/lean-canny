/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalTower

/-! # Collected indexed rows of affine-height towers

Every source block, multiplier, and referenced ancestral height has its exact
stage-order finite index. The complete indexed system has the stated original
source, gradient, and linear-height rows, with no ancestor elimination step.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalIndexedRows
open MvPolynomial FlatAffineCriticalTower
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {n d : ℕ} {R : Type*} [CommRing R]

def current (k : ℕ) (hk : k < d) (i : Fin n) : Fin (d * width n) :=
  TriangularPolynomialRows.block (width n) k d hk (blockEquiv n (Sum.inl i))
def multiplier (k : ℕ) (hk : k < d) (j : Fin (n + 1)) : Fin (d * width n) :=
  TriangularPolynomialRows.block (width n) k d hk (blockEquiv n (Sum.inr j))

def embedding (k : ℕ) (hk : k < d) :
    (Ancestors n k ⊕ FlatAffineCriticalStage.Variables n) → Fin (d * width n) :=
  TriangularPolynomialRows.embedding (width n) k d hk ∘
    (Equiv.sumCongr (Equiv.refl (Ancestors n k)) (blockEquiv n))

theorem embedding_ambient (k : ℕ) (hk : k < d) (i : Fin n) :
    embedding k hk (FlatAffineCriticalStage.ambient i) = current k hk i :=
  TriangularPolynomialRows.embedding_current (width n) k d hk _

theorem embedding_multiplier (k : ℕ) (hk : k < d) (j : Fin (n + 1)) :
    embedding k hk (FlatAffineCriticalStage.multiplier j) = multiplier k hk j :=
  TriangularPolynomialRows.embedding_current (width n) k d hk _

theorem embedding_old (k : ℕ) (hk : k < d) (m : Fin k) (i : Fin n) :
    embedding k hk (Sum.inl (oldAmbient k m i)) = current m.val (m.isLt.trans hk) i := by
  apply Fin.ext
  change (TriangularPolynomialIndexing.enumerate (width n) (k + 1) (Sum.inl (oldAmbient k m i))).val = _
  rw [TriangularPolynomialIndexing.enumerate_old, oldAmbient_index]
  rfl

theorem current_shift (k : ℕ) (hk : k < d) : current (n := n) k hk =
    BlockRenameCoefficient.shift n (d * width n) (k * width n) (by
      have H := Nat.mul_le_mul_right (width n) hk
      have hn : n ≤ width n := by unfold width; omega
      rw [Nat.succ_mul] at H
      omega) := by
  funext i
  rfl

variable (p : MvPolynomial (Fin n) R) (s : ℕ → Finset (Fin n))
  (a : ℕ → Fin (n + 1) → Fin n → R) (b : (k : ℕ) → Fin n → Level n k R)

theorem stage_row (k : ℕ) (hk : k < d) (j : FlatAffineCriticalStage.Variables n) :
    system p s a b d (TriangularPolynomialRows.block (width n) k d hk (blockEquiv n j)) =
      rename (embedding k hk) (FlatAffineCriticalStage.row p (s k) (a k) (fun i => (b k i).polynomial) j) := by
  rw [system, TriangularPolynomialRows.stage_row]
  simp only [family, Equiv.symm_apply_apply, rename_rename]
  rfl

theorem rename_height (k : ℕ) (hk : k < d) (v : Fin n → R) :
    rename (embedding k hk) (AffineHeightPolynomial.polynomial v FlatAffineCriticalStage.ambient) =
      AffineHeightPolynomial.polynomial v (current k hk) := by
  simp only [AffineHeightPolynomial.polynomial, map_sum, map_mul, rename_C, rename_X, embedding_ambient]

theorem rename_level (k : ℕ) (hk : k < d) (v : Level n k R) :
    rename (embedding k hk) (rename Sum.inl v.polynomial) =
      match v with
      | .constant c => C c
      | .height m v => AffineHeightPolynomial.polynomial v (current m.val (m.isLt.trans hk))
      | .midpoint l r v => AffineHeightPolynomial.polynomial v (current l.val (l.isLt.trans hk)) +
          AffineHeightPolynomial.polynomial v (current r.val (r.isLt.trans hk)) := by
  cases v <;> simp only [Level.polynomial, AffineHeightPolynomial.midpointLevel,
    AffineHeightPolynomial.polynomial, map_sum, map_add, map_mul, rename_C, rename_X, embedding_old]

theorem source_row (k : ℕ) (hk : k < d) :
    system p s a b d (multiplier k hk 0) = rename (current k hk) p := by
  rw [multiplier, stage_row]
  simp only [FlatAffineCriticalStage.row, Fin.cases_zero, rename_rename]
  apply congrArg (fun f => rename f p)
  funext i
  exact embedding_ambient k hk i

theorem gradient_row (k : ℕ) (hk : k < d) (i : Fin n) :
    system p s a b d (current k hk i) = rename (current k hk) (pderiv i p) -
      ∑ j, C (a k j i) * X (multiplier k hk j) := by
  rw [current, stage_row]
  simp only [FlatAffineCriticalStage.row, FlatAffineCriticalStage.gradient, map_sub, map_sum,
    map_mul, rename_C, rename_X, embedding_multiplier, rename_rename]
  congr 1

theorem level_row (k : ℕ) (hk : k < d) (j : Fin n) :
    system p s a b d (multiplier k hk j.succ) =
      if j ∈ s k then AffineHeightPolynomial.polynomial (a k j.succ) (current k hk) -
        rename (embedding k hk) (rename Sum.inl (b k j).polynomial)
      else X (multiplier k hk j.succ) := by
  rw [multiplier, stage_row]
  simp only [FlatAffineCriticalStage.row, Fin.cases_succ]
  split_ifs <;> simp only [map_sub, rename_height, rename_X, embedding_multiplier]
  rfl

end LeanCanny.Algebra.FlatAffineCriticalIndexedRows
