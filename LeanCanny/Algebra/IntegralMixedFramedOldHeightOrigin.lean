/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryOrigin
public import LeanCanny.Algebra.CommonHeightResidueFP
/-! # Changing-source retained heights reduce to their original creating companions -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation UniformIntegralPrefix IntegralMixedHistory
open scoped Classical
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
set_option backward.isDefEq.respectTransparency false

theorem Origin.radix_eq {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length ≤ S + 1} {i : Fin cs.length} (o : Origin initial cs h i) :
    o.chain.radix = FixedWidthPolynomial.count i.val B := by
  unfold UniformIntegralPrefix.Chain.radix
  rw [o.length_eq]
  rfl

theorem Origin.oldIndex_val {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length ≤ S + 1} {i : Fin cs.length} (o : Origin initial cs h i)
    (r : Fin (FixedWidthPolynomial.count cs.length B)) :
    (o.chain.oldIndex r).val = r.val / FixedWidthPolynomial.count i.val B := by
  change r.val / o.chain.radix = _
  rw [o.radix_eq]

theorem Origin.cleared_matrix {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length ≤ S + 1} {i : Fin cs.length} (o : Origin initial cs h i)
    (hc : Canonical (run initial cs h)) (r t : Fin (FixedWidthPolynomial.count cs.length B)) :
    Algebra.leftMulMatrix (run initial cs h).sampler.scalarPrefix.basis.finBasis
      (cleared (run initial cs h) i) r t =
      CommonIntegerDenominator.denominator (Finset.univ.erase i) (run initial cs h).bank.denominator *
        (if r.val % FixedWidthPolynomial.count i.val B = t.val % FixedWidthPolynomial.count i.val B then
          Algebra.leftMulMatrix (birthPrefix initial cs h i).basis.finBasis
            (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) else 0) := by
  unfold cleared CommonIntegerDenominator.numerator
  rw [CommonHeightBits.numerator_matrix, hc i, o.matrix, o.radix_eq]

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
