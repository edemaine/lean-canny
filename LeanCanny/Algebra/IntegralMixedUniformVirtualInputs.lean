/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCoordinateBounds

/-! # One native height exponent for the actual virtual input rows

All four original virtual-source input bounds follow from the retained
bank and original spatial syntax. Raising them to one native exponent
lets the original low-row and gradient-row bounds be used directly,
without supplying new matrix height or coefficient reader assumptions.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedUniformVirtualInputs
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateBounds
open scoped Classical

def height (F : Family) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  inputFactor (F.ambient q) (F.cap q) (H.nodes q) * H.bankHeight q

theorem height_binary (F : Family) (H : OriginalBounds F)
    (hn : UnaryFn F.ambient) (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (height F H) :=
  (((BinaryFn.ofUnary hn).add (BinaryFn.const 2)).mul
    ((hL.add (BinaryFn.const 1)).mul (hS.add (BinaryFn.const 3)))).mul hG

theorem height_le (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (H : OriginalBounds F) (q : List Bool) :
    let B := IntegralMixedVirtualBounds.inputs F I H.bankHeight H.sourceHeight H.bank H.coefficient
    B.coefficientHeight q ≤ height F H q ∧ B.retainedHeight q ≤ height F H q ∧
      B.denominatorHeight q ≤ height F H q ∧ B.leadingHeight q ≤ height F H q := by
  have HE := IntegralMixedGlobalHeightBounds.expressionFactor_pos (F.cap q) (H.nodes q)
  have HG : H.bankHeight q ≤ height F H q := by
    have HF : 1 ≤ inputFactor (F.ambient q) (F.cap q) (H.nodes q) := by unfold inputFactor; nlinarith
    simpa only [height, Nat.one_mul] using Nat.mul_le_mul_right (H.bankHeight q) HF
  have HC : H.sourceHeight q ≤ height F H q :=
    (Nat.le_succ _).trans ((H.source_le_bank q).trans HG)
  have HV := retainedHeight_scaled (F.rule q) (F.birth q) (F.cap q) (H.nodes q)
    (H.sourceHeight q) (H.bankHeight q) (F.birth_bound q) (H.expression_nodes q)
    (H.expression_coefficients q) (H.scales q) (H.slope q) (H.source_le_bank q)
  have HQ : (F.ambient q + 1) * IntegralMixedVirtualBounds.scaleHeight (F.birth q) (H.bankHeight q) (F.rule q) ≤
      height F H q := by
    have HS := scaleHeight_scaled (F.rule q) (F.birth q) (F.cap q) (H.nodes q)
      (H.sourceHeight q) (H.bankHeight q) (F.birth_bound q) (H.scales q) (H.source_le_bank q)
    unfold height inputFactor
    nlinarith
  exact ⟨HC, HV, HQ, (H.leading q).trans HC⟩

noncomputable def inputs (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (H : OriginalBounds F) :
    IntegralOriginalCriticalBounds.Inputs (IntegralMixedVirtualSweepSource.source F I) where
  coefficientHeight := height F H
  retainedHeight := height F H
  denominatorHeight := height F H
  leadingHeight := height F H
  coefficient q e u v :=
    ((IntegralMixedVirtualBounds.inputs F I H.bankHeight H.sourceHeight H.bank H.coefficient).coefficient q e u v).trans
      (Nat.pow_le_pow_right (by decide) (height_le F I H q).1)
  retained q i u v :=
    ((IntegralMixedVirtualBounds.inputs F I H.bankHeight H.sourceHeight H.bank H.coefficient).retained q i u v).trans
      (Nat.pow_le_pow_right (by decide) (height_le F I H q).2.1)
  denominator q :=
    ((IntegralMixedVirtualBounds.inputs F I H.bankHeight H.sourceHeight H.bank H.coefficient).denominator q).trans
      (Nat.pow_le_pow_right (by decide) (height_le F I H q).2.2.1)
  leading q :=
    ((IntegralMixedVirtualBounds.inputs F I H.bankHeight H.sourceHeight H.bank H.coefficient).leading q).trans
      (Nat.pow_le_pow_right (by decide) (height_le F I H q).2.2.2)

end LeanCanny.Algebra.IntegralMixedUniformVirtualInputs
