/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableCoordinatesWith

/-! # Prepared family coordinates with source-derived fixed clearing envelopes -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableFinite.Family
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair SymbolicFixedTable
open scoped Classical

def fixedBase (F : Family) : ℕ := F.budget.degree + 1 + F.budget.innerDegree + F.budget.massExponent + 4

theorem fixedBase_four (F : Family) : 4 ≤ fixedBase F := by unfold fixedBase; omega

theorem fixedSource_bounded (F : Family) : F.paddedBudget.BoundedBy (fixedBase F) := by
  unfold Budget.BoundedBy paddedBudget fixedBase
  dsimp only
  omega

theorem fixedBase_le_pow (F : Family) : fixedBase F ≤ fixedBase F ^ 16 := by
  simpa only [pow_one] using Nat.pow_le_pow_right (n := fixedBase F) (by have := fixedBase_four F; omega) (show 1 ≤ 16 by decide)

theorem fixedEnvelope_le (F : Family) : (fixedBase F ^ 16) ^ (16 ^ F.count.size) ≤ F.exponent := by
  rw [exponent_eq]
  change _ ≤ fixedBase F ^ (65536 * (F.count + 1) ^ 4)
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by have := fixedBase_four F; omega)
  rw [show 16 * 16 ^ F.count.size = 16 ^ (F.count.size + 1) by rw [pow_succ]; omega]
  exact (FiniteAnnihilatorTree.heightExponent_le F.count).trans
    (Nat.mul_le_mul_right _ (by decide : 256 ≤ 65536))

noncomputable def fixedCoordinate (F : Family) (i : Fin F.count) : SymbolicBalancedCoordinate.Coordinate :=
  coordinateWith (F.fixedBase ^ 16) (fun j => SymbolicScaledSquarefree.polynomial (F.padded j))
    F.directions F.count.size 0 i.val

theorem fixedCoordinate_bounds (F : Family) (i : Fin F.count) : CoordinateBounds (F.fixedCoordinate i) F.exponent := by
  have hc := coordinateWith_uniform F.paddedBudget.squarefree
    (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions
    (fun i => F.paddedBudget.squarefree_controls _ (F.padded_controls i))
    (F.reference.admissible _ F.padded_controls F.padded_nonzero) (fixedBase F ^ 16)
    ((fixedBase_four F).trans (fixedBase_le_pow F))
    (F.paddedBudget.squarefree_bounded (fixedBase F) (fixedBase_four F) (fixedSource_bounded F)) F.count.size 0 i.val
  exact hc.mono (fixedEnvelope_le F)


theorem fixedCoordinate_spec (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (theta : ℝ)
    (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) (i : Fin F.count) :
    (F.fixedCoordinate i).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (F.fixedCoordinate i).eval (scalarEvaluation beta) theta = F.decode beta theta i := by
  exact coordinateWith_spec F.paddedBudget.squarefree _ _ (F.fixedBase ^ 16)
    ((fixedBase_four F).trans (fixedBase_le_pow F))
    (F.paddedBudget.squarefree_bounded _ (fixedBase_four F) (fixedSource_bounded F))
    (fun j => F.paddedBudget.squarefree_controls _ (F.padded_controls j))
    (F.reference.admissible _ F.padded_controls F.padded_nonzero) F.count.size
    (F.reference.separableTable _ F.padded_controls F.padded_nonzero) beta hb
    (he.trans (dyadic_antitone F.reference.tree_sufficient)) F.count.size 0 i.val le_rfl
    (i.isLt.trans (Nat.lt_size_self _)) theta ht

end LeanCanny.Algebra.SymbolicFixedTableFinite.Family
