/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulNonpivotBlocks
public import Mathlib.Order.Prod.Lex.Basic

/-! # Determinant products for weighted finite block labels

If nonzero entries can only increase a label's weight, and can preserve the
weight only inside a single label, a finite ordering refining the weights
makes the matrix block triangular. Its determinant is the product of the
principal block determinants for the original labels.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixBlockProduct
open scoped BigOperators Classical Matrix
variable {R S T : Type*} [CommRing R] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

theorem determinant_of_weight (M : Matrix S S R) (b : S → T) (w : T → ℕ)
    (hmono : ∀ i j, M i j ≠ 0 → w (b i) ≤ w (b j))
    (hequal : ∀ i j, M i j ≠ 0 → w (b i) = w (b j) → b i = b j) :
    M.det = ∏ t : T, (M.toSquareBlock b t).det := by
  let e : T → Lex (ℕ × Fin (Fintype.card T)) := fun t => toLex (w t, Fintype.equivFin T t)
  have hinj : Function.Injective e := by
    intro x y he
    exact (Fintype.equivFin T).injective (congrArg (fun z : Lex (ℕ × Fin (Fintype.card T)) => (ofLex z).2) he)
  let : LinearOrder T := LinearOrder.lift' e hinj
  have htri : M.BlockTriangular b := by
    intro i j hlt
    change e (b j) < e (b i) at hlt
    by_contra hz
    have hw := hmono i j hz
    by_cases he : w (b i) = w (b j)
    · have hb := congrArg e (hequal i j hz he)
      exact hlt.ne hb.symm
    · have hs : w (b i) < w (b j) := lt_of_le_of_ne hw he
      have hl : e (b i) < e (b j) := (Prod.Lex.toLex_lt_toLex).mpr (Or.inl hs)
      exact (not_lt_of_ge hl.le) hlt
  have hd := determinant M b htri
  refine hd.trans ?_
  apply Finset.prod_congr rfl
  intro t _
  exact det_fintype_congr _ _ _

end LeanCanny.Algebra.MatrixBlockProduct
