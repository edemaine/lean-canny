/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableFiniteWith
public import LeanCanny.Algebra.SymbolicCoordinatePathMatrix
public import LeanCanny.Algebra.BalancedLeafPath

/-! # Exact routing from a fixed-envelope coordinate to its ascending leaf path -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicBalancedCoordinate
open BalancedLeafPath (ancestor ancestor_split residue_split)
open scoped Classical

noncomputable def leafStep (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ) (j h : ℕ) : Coordinate :=
  let i := ancestor j (h + 1)
  pairCoordinate (decide (ancestor j h % 2 = 1))
    (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i)

theorem path_eq_coordinateWith (T : ℕ) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ) (j h : ℕ) :
    SymbolicCoordinatePath.path (fun s => T ^ (16 ^ s)) (leafStep a c j) h =
      coordinateWith T a c h (ancestor j h) (j % 2 ^ h) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have ha := ancestor_split j h
    have hsmall := Nat.mod_lt j (Nat.two_pow_pos h)
    rcases Nat.mod_two_eq_zero_or_one (ancestor j h) with hz | ho
    · have hai : ancestor j h = 2 * ancestor j (h + 1) := by omega
      have hres : j % 2 ^ (h + 1) = j % 2 ^ h := by rw [residue_split, hz, zero_mul, zero_add]
      rw [SymbolicCoordinatePath.path, ih, coordinateWith, hres, ite_eq_left hsmall, hai]
      simp only [leafStep, hz, Nat.zero_ne_one, decide_false]
    · have hai : ancestor j h = 2 * ancestor j (h + 1) + 1 := by omega
      have hres : j % 2 ^ (h + 1) = 2 ^ h + j % 2 ^ h := by rw [residue_split, ho, one_mul]
      have hn : ¬j % 2 ^ (h + 1) < 2 ^ h := by omega
      rw [SymbolicCoordinatePath.path, ih, coordinateWith, ite_eq_right hn, hres, Nat.add_sub_cancel_left, hai]
      simp only [leafStep, ho, decide_true]

end LeanCanny.Algebra.SymbolicFixedTable

namespace LeanCanny.Algebra.SymbolicFixedTableFinite.Family
open SymbolicFixedTable SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical

theorem fixedCoordinate_eq_path (F : Family) (i : Fin F.count) : F.fixedCoordinate i =
    SymbolicCoordinatePath.path (fun s => (F.fixedBase ^ 16) ^ (16 ^ s))
      (leafStep (fun j => SymbolicScaledSquarefree.polynomial (F.padded j)) F.directions i.val) F.count.size := by
  rw [path_eq_coordinateWith]
  have hi := i.isLt.trans (Nat.lt_size_self F.count)
  simp only [BalancedLeafPath.ancestor, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, fixedCoordinate]

theorem leafStep_bounds (F : Family) (j h : ℕ) (hh : h < F.count.size) :
    CoordinateBounds (leafStep (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions j h) F.exponent := by
  let B := F.paddedBudget.squarefree
  let T := F.fixedBase ^ 16
  have hT : 4 ≤ T := (F.fixedBase_four).trans (F.fixedBase_le_pow)
  have hB : B.BoundedBy T := F.paddedBudget.squarefree_bounded F.fixedBase F.fixedBase_four F.fixedSource_bounded
  have ha (i) : B.Controls (SymbolicScaledSquarefree.polynomial (F.padded i)) :=
    F.paddedBudget.squarefree_controls _ (F.padded_controls i)
  have hc : Admissible B F.directions := F.reference.admissible _ F.padded_controls F.padded_nonzero
  have hTb : 4 ≤ T ^ (16 ^ h) := by
    apply hT.trans
    simpa only [pow_one] using Nat.pow_le_pow_right (n := T) (by omega) (Nat.one_le_pow h 16 (by decide))
  have hb := treeBudget_bounded B T hT hB h
  have hp := node_controls B (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions ha hc h
  have he : (T ^ (16 ^ h)) ^ 12 ≤ F.exponent := by
    apply le_trans ?_ F.fixedEnvelope_le
    change (T ^ (16 ^ h)) ^ 12 ≤ T ^ (16 ^ F.count.size)
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    calc
      _ ≤ 16 ^ h * 16 := Nat.mul_le_mul_left _ (by decide)
      _ = 16 ^ (h + 1) := (pow_succ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  exact (pairCoordinate_bounds (treeBudget B h) _ hTb hb _ _
    (hp _) (hp _) _ (hc h (BalancedLeafPath.ancestor j (h + 1)))
    (decide (BalancedLeafPath.ancestor j h % 2 = 1))).mono he

end LeanCanny.Algebra.SymbolicFixedTableFinite.Family
