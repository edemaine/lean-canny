/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFactorCeiling
public import LeanCanny.Algebra.IntegralCoefficientBlocks

/-! # Numeric query caps for canonical critical stages

One binary cap includes the spatial grids, old rank, scalar width, height
budget, modulus, and the matrix dimensions used by the recursive stages.
The height budget itself is a field bound; its exponential is never put in
a query word. Polynomial unary arities give a native binary cap.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalQueryBounds
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

def cap (S n R W D N C m : ℕ) : ℕ :=
  1 + S + n + R + W + D + N + C + m + FixedWidthPolynomial.count n W +
    PurePowerReductionBounds.dimension n D + (PurePowerReductionBounds.bound n D + 1) +
    (PurePowerReductionBounds.bound n D + 1) * PurePowerReductionBounds.dimension n D +
    IntegralCoefficientBlocks.dimension (PurePowerReductionBounds.dimension n D) R +
    (PurePowerReductionBounds.dimension n D + 2) * R + PurePowerReductionBounds.dimension n D * R +
    (n + 3) * R + R ^ (n + 3)

theorem cap_binary {S n R W D N C m : List Bool → ℕ} (hS : BinaryFn S) (hn : UnaryFn n) (hR : BinaryFn R)
    (hW : UnaryFn W) (hD : BinaryFn D) (hN : BinaryFn N) (hC : BinaryFn C) (hm : BinaryFn m) :
    BinaryFn (fun q => cap (S q) (n q) (R q) (W q) (D q) (N q) (C q) (m q)) := by
  have HG : BinaryFn (fun q => FixedWidthPolynomial.count (n q) (W q)) :=
    (BinaryFn.fromBits (FixedWidthPolynomial.countCode_mem_FP hn hW)).of_eq
      (fun q => by rw [FixedWidthPolynomial.countCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  have HL := PurePowerReductionBounds.dimension_binary hn hD
  have HB := (PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary hn) hD).add (BinaryFn.const 1)
  exact (((((((((((((((((BinaryFn.const 1).add hS).add (BinaryFn.ofUnary hn)).add hR).add (BinaryFn.ofUnary hW)).add hD).add hN).add hC).add hm).add HG).add HL).add HB).add (HB.mul HL)).add
    (IntegralCoefficientBlocks.dimension_binary HL hR)).add ((HL.add (BinaryFn.const 2)).mul hR)).add (HL.mul hR)).add
    (((BinaryFn.ofUnary hn).add (BinaryFn.const 3)).mul hR)).add (hR.powUnary (hn.add (UnaryFn.const 3)))

variable (S n R W D N C m : ℕ)

theorem metadata_le : S ≤ cap S n R W D N C m ∧ n ≤ cap S n R W D N C m ∧ R ≤ cap S n R W D N C m ∧
    W ≤ cap S n R W D N C m ∧ D ≤ cap S n R W D N C m ∧ N ≤ cap S n R W D N C m ∧
    C ≤ cap S n R W D N C m ∧ m ≤ cap S n R W D N C m := by
  unfold cap
  omega

theorem source_grid_le : FixedWidthPolynomial.count n W ≤ cap S n R W D N C m := by unfold cap; omega

theorem spatial_grid_le : PurePowerReductionBounds.dimension n D ≤ cap S n R W D N C m := by unfold cap; omega

theorem reduction_exponent_le : PurePowerReductionBounds.bound n D + 1 ≤ cap S n R W D N C m := by unfold cap; omega

theorem coefficient_block_le : IntegralCoefficientBlocks.dimension (PurePowerReductionBounds.dimension n D) R ≤
    cap S n R W D N C m := by unfold cap; omega

theorem moment_block_le : (PurePowerReductionBounds.dimension n D + 2) * R ≤ cap S n R W D N C m := by unfold cap; omega

theorem action_block_le : PurePowerReductionBounds.dimension n D * R ≤ cap S n R W D N C m := by unfold cap; omega

theorem product_block_le : (n + 3) * R ≤ cap S n R W D N C m := by unfold cap; omega

theorem retained_grid_le : R ^ (n + 3) ≤ cap S n R W D N C m := by unfold cap; omega

theorem scale_exponent_le {b k : ℕ} (hb : b ≤ PurePowerReductionBounds.bound n D)
    (hk : k ≤ PurePowerReductionBounds.dimension n D) : (b + 1) * k ≤ cap S n R W D N C m := by
  have H := Nat.mul_le_mul (Nat.add_le_add_right hb 1) hk
  unfold cap
  omega

theorem coefficient_block_le_of_le {L r : ℕ} (hL : L ≤ PurePowerReductionBounds.dimension n D) (hr : r ≤ R) :
    IntegralCoefficientBlocks.dimension L r ≤ cap S n R W D N C m := by
  apply le_trans _ (coefficient_block_le S n R W D N C m)
  unfold IntegralCoefficientBlocks.dimension
  gcongr

theorem moment_block_le_of_le {L r : ℕ} (hL : L ≤ PurePowerReductionBounds.dimension n D) (hr : r ≤ R) :
    (L + 2) * r ≤ cap S n R W D N C m :=
  (Nat.mul_le_mul (Nat.add_le_add_right hL 2) hr).trans (moment_block_le S n R W D N C m)

theorem product_block_le_of_le {count r : ℕ} (hc : count ≤ n + 2) (hr : r ≤ R) :
    (count + 1) * r ≤ cap S n R W D N C m := by
  apply le_trans _ (product_block_le S n R W D N C m)
  apply Nat.mul_le_mul _ hr
  omega

theorem source_grid_le_of_le {a w : ℕ} (ha : a ≤ n) (hw : w ≤ W) :
    FixedWidthPolynomial.count a w ≤ cap S n R W D N C m := by
  apply le_trans _ (source_grid_le S n R W D N C m)
  unfold FixedWidthPolynomial.count
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hw ha)

end LeanCanny.Algebra.IntegralCriticalQueryBounds
