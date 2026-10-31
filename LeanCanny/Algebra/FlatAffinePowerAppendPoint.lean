/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerPrefix
public import LeanCanny.Algebra.FlatAffineTowerRegularity

/-! # Multiplier powers commute with appending one critical block -/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineTowerRegularity
open FlatAffineCriticalTower
variable {n k : ℕ} {K : Type*}

theorem appendPoint_prefix_of_le {d : ℕ} (hd : d ≤ k) (x : Fin (k * width n) → K)
    (y : FlatAffineCriticalStage.Variables n → K) :
    appendPoint k x y ∘ TriangularPolynomialRows.prefixIndex (width n) d (k + 1) (by omega) =
      x ∘ TriangularPolynomialRows.prefixIndex (width n) d k hd := by
  funext i
  exact congrFun (appendPoint_prefix k x y) (TriangularPolynomialRows.prefixIndex (width n) d k hd i)

theorem appendPoint_old_block (x : Fin (k * width n) → K) (y : FlatAffineCriticalStage.Variables n → K)
    (t : Fin k) (v : FlatAffineCriticalStage.Variables n) :
    appendPoint k x y (TriangularPolynomialRows.block (width n) t.val (k + 1) (by omega) (blockEquiv n v)) =
      x (TriangularPolynomialRows.block (width n) t.val k t.isLt (blockEquiv n v)) :=
  congrFun (appendPoint_prefix k x y) (TriangularPolynomialRows.block (width n) t.val k t.isLt (blockEquiv n v))

theorem append_point_ext (x y : Fin ((k + 1) * width n) → K)
    (hold : x ∘ TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega) =
      y ∘ TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega))
    (hnew : ∀ v : FlatAffineCriticalStage.Variables n,
      x (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)) =
        y (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v))) : x = y := by
  funext i
  obtain ⟨j, rfl⟩ := (TriangularPolynomialIndexing.enumerate (width n) (k + 1)).surjective i
  cases j with
  | inl j =>
    have H : TriangularPolynomialIndexing.enumerate (width n) (k + 1) (Sum.inl j) =
        TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega)
          (TriangularPolynomialIndexing.enumerate (width n) k j) :=
      Fin.ext (TriangularPolynomialIndexing.enumerate_old (width n) k j)
    rw [H]
    exact congrFun hold (TriangularPolynomialIndexing.enumerate (width n) k j)
  | inr j =>
    obtain ⟨v, rfl⟩ := (blockEquiv n).surjective j
    have H : TriangularPolynomialIndexing.enumerate (width n) (k + 1) (Sum.inr (blockEquiv n v)) =
        TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v) :=
      Fin.ext (TriangularPolynomialIndexing.enumerate_new (width n) k (blockEquiv n v))
    rw [H]
    exact hnew v

end LeanCanny.Algebra.FlatAffineTowerRegularity

namespace LeanCanny.Algebra.FlatAffinePowerTower
open FlatAffineCriticalTower FlatAffineCriticalStage FlatAffineTowerRegularity
variable {n k : ℕ} {K : Type*} [Monoid K]

def blockPower (D : ℕ) (v : Variables n → K) : Variables n → K
  | .inl i => v (Sum.inl i)
  | .inr r => v (Sum.inr r) ^ (D - 1)

theorem powerPoint_block (D : ℕ) (z : Index n k → K) (t : Fin k) (v : Variables n) :
    powerPoint D z (TriangularPolynomialRows.block (width n) t.val k t.isLt (blockEquiv n v)) =
      blockPower D (fun w => z (TriangularPolynomialRows.block (width n) t.val k t.isLt (blockEquiv n w))) v := by
  simp only [← row_index_eq, powerPoint, Equiv.symm_apply_apply]
  cases v <;> rfl

theorem powerPoint_appendPoint (D : ℕ) (x : Index n k → K) (v : Variables n → K) :
    powerPoint D (appendPoint k x v) = appendPoint k (powerPoint D x) (blockPower D v) := by
  apply append_point_ext
  · have H := powerPoint_prefix (n := n) (d := k) (k := k + 1) (by omega) D (appendPoint k x v)
    have E := congrArg (powerPoint D) (appendPoint_prefix k x v)
    exact (H.symm.trans E).trans (appendPoint_prefix k (powerPoint D x) (blockPower D v)).symm
  · intro w
    have H : (fun j : Variables n => appendPoint k x v
        (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n j))) = v :=
      funext (appendPoint_new k x v)
    exact (powerPoint_block D (appendPoint k x v) ⟨k, by omega⟩ w).trans
      ((congrArg (fun f : Variables n → K => blockPower D f w) H).trans
        (appendPoint_new k (powerPoint D x) (blockPower D v) w).symm)

end LeanCanny.Algebra.FlatAffinePowerTower
