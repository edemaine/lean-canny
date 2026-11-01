/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCoordinateBounds
public import LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource

/-! # One original-source height for all virtual coordinate rows

The same bound applies to every actual coordinate polynomial in a Gram
grid. The auxiliary selector is used only to instantiate a valid finite
coordinate; no incoming external label is replaced in a decision routine.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualCoordinateBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateBounds
open IntegralMixedVirtualSweepSource

def select (F : Family) (I : Indices F) (j : ℕ) : Indices F :=
  { I with coordinate q := ⟨j % (F.ambient q - (F.rule q).critical.offset.val + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩ }

def height (F : Family) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  IntegralMixedCoordinateBounds.height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
    (F.cap q) (H.nodes q) (H.bankHeight q)

theorem coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (k : ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).coeff k) u v).natAbs ≤
        2 ^ height F H q := by
  have HJ : (select F I j.val).coordinate q = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  have HE := IntegralMixedVirtualBounds.coefficient_height F (select F I j.val)
    H.bankHeight H.sourceHeight H.bank H.coefficient q k u v
  rw [HJ] at HE
  rw [IntegralMixedSquarefreeMatrixSource.coordinateImage, Polynomial.coeff_map]
  exact HE.trans (Nat.pow_le_pow_right (by decide)
    (budget_le F (select F I j.val) H.bankHeight H.sourceHeight H.bank H.coefficient q
      (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (H.nodes q) (H.rank_bound q)
      (H.width_bound q) (H.degree_bound q) (H.leading q) (H.expression_nodes q)
      (H.expression_coefficients q) (H.scales q) (H.slope q) (H.source_le_bank q)))

theorem height_binary (F : Family) (H : OriginalBounds F)
    (hn : UnaryFn F.ambient) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (height F H) := IntegralMixedCoordinateBounds.height_binary hn hM hW hD hS hL hG

end LeanCanny.Algebra.IntegralMixedVirtualCoordinateBounds
