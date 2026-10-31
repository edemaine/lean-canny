/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralOriginalCriticalFactorBounds
public import LeanCanny.Algebra.PurePowerReductionBounds

/-! # One metadata ceiling for all critical height factors

A bound on the original arity, scalar rank, source width, and local degree
bounds every canonical free-coordinate reduction. This permits one factor
to be fixed before following a bounded retained history.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFactorCeiling
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem bound_mono {n N D E : ℕ} (hn : n ≤ N) (hD : D ≤ E) :
    PurePowerReductionBounds.bound n D ≤ PurePowerReductionBounds.bound N E := by
  unfold PurePowerReductionBounds.bound
  exact Nat.add_le_add_right (Nat.mul_le_mul hn (Nat.sub_le_sub_right hD 1)) 1

theorem width_mono {n N D E : ℕ} (hn : n ≤ N) (hD : D ≤ E) :
    PurePowerReductionBounds.width n D ≤ PurePowerReductionBounds.width N E :=
  Nat.size_le_size (Nat.add_le_add_right (bound_mono hn hD) 1)

theorem dimension_mono {n N D E : ℕ} (hn : n ≤ N) (hD : D ≤ E) :
    PurePowerReductionBounds.dimension n D ≤ PurePowerReductionBounds.dimension N E := by
  unfold PurePowerReductionBounds.dimension FixedWidthPolynomial.count
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul (width_mono hn hD) hn)

def lower (n M W D : ℕ) : ℕ :=
  IntegralFrozenConstantBounds.lowerHeight n M W D 1 1 1 1 + D.size +
    IntegralFrozenCoefficientBounds.coefficientHeight n M W D (1 + W) 1 1 + n.size + 1

def leading (D : ℕ) : ℕ := 1 + D + D.size

def factor (n M W D : ℕ) : ℕ :=
  IntegralActionHeightBounds.criticalFactor (PurePowerReductionBounds.dimension n D) M
    (PurePowerReductionBounds.bound n D) * (lower n M W D + 2 * leading D + 1)

theorem lower_mono {n N M R W V D E : ℕ} (hn : n ≤ N) (hM : M ≤ R) (hW : W ≤ V) (hD : D ≤ E) :
    lower n M W D ≤ lower N R V E := by
  unfold lower IntegralFrozenConstantBounds.lowerHeight IntegralFrozenConstantBounds.constantHeight
    IntegralFrozenConstantBounds.sumHeight IntegralFrozenCoefficientBounds.coefficientHeight
    IntegralFrozenCoefficientBounds.termHeight
  gcongr <;> exact Nat.size_le_size (by omega)

theorem leading_mono {D E : ℕ} (hD : D ≤ E) : leading D ≤ leading E := by
  unfold leading
  exact Nat.add_le_add (Nat.add_le_add_left hD 1) (Nat.size_le_size hD)

theorem actionFactor_mono {L K M R b d : ℕ} (hL : L ≤ K) (hM : M ≤ R) (hb : b ≤ d) :
    IntegralActionHeightBounds.criticalFactor L M b ≤ IntegralActionHeightBounds.criticalFactor K R d := by
  unfold IntegralActionHeightBounds.criticalFactor
  gcongr <;> first | exact Nat.size_le_size (by omega) | exact Nat.size_le_size (Nat.mul_le_mul hL hM)

theorem factor_binary {n M W D : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) : BinaryFn (fun c => factor (n c) (M c) (W c) (D c)) := by
  have HS := IntegralFrozenConstantBounds.lowerHeight_binary (BinaryFn.ofUnary hn) hM hW hD
    (BinaryFn.const 1) (BinaryFn.const 1) (BinaryFn.const 1) (BinaryFn.const 1)
  have HG := IntegralFrozenCoefficientBounds.coefficientHeight_binary (BinaryFn.ofUnary hn) hM hW hD
    ((BinaryFn.const 1).add (BinaryFn.ofUnary hW)) (BinaryFn.const 1) (BinaryFn.const 1)
  have HL : BinaryFn (fun c => lower (n c) (M c) (W c) (D c)) :=
    (((HS.add hD.size).add HG).add (BinaryFn.ofUnary hn).size).add (BinaryFn.const 1)
  have HP : BinaryFn (fun c => leading (D c)) := ((BinaryFn.const 1).add hD).add hD.size
  exact (IntegralActionHeightBounds.criticalFactor_binary (PurePowerReductionBounds.dimension_binary hn hD) hM
    (PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary hn) hD)).mul
      ((HL.add ((BinaryFn.const 2).mul HP)).add (BinaryFn.const 1))

theorem dominates (S : IntegralClearedCriticalBits.Source) (c : List Bool) (n M W D : ℕ)
    (hn : S.arity c ≤ n) (hf : S.free c ≤ n) (hM : S.rank c ≤ M) (hW : S.sourceWidth c ≤ W)
    (hD : S.allowance c ≤ D)
    (hL : IntegralClearedCriticalBounds.dimension S c ≤ PurePowerReductionBounds.dimension n D)
    (hb : S.bound c ≤ PurePowerReductionBounds.bound n D) :
    IntegralOriginalCriticalFactorBounds.factor S c ≤ factor n M W D := by
  have HL : IntegralOriginalCriticalFactorBounds.lowerTemplate S c ≤ lower n M W D := by
    unfold IntegralOriginalCriticalFactorBounds.lowerTemplate IntegralOriginalCriticalFactorBounds.sourceTemplate
      IntegralOriginalCriticalFactorBounds.gradientTemplate lower
      IntegralFrozenConstantBounds.lowerHeight IntegralFrozenConstantBounds.constantHeight
      IntegralFrozenConstantBounds.sumHeight IntegralFrozenCoefficientBounds.coefficientHeight
      IntegralFrozenCoefficientBounds.termHeight
    gcongr <;> exact Nat.size_le_size (by omega)
  have HP : IntegralOriginalCriticalFactorBounds.leadingTemplate S c ≤ leading D := leading_mono hD
  exact Nat.mul_le_mul (actionFactor_mono hL hM hb)
    (Nat.add_le_add_right (Nat.add_le_add HL (Nat.mul_le_mul_left 2 HP)) 1)

end LeanCanny.Algebra.IntegralCriticalFactorCeiling
