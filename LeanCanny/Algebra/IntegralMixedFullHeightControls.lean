/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullRunHeight
/-! # Native binary controls for the full-history original-only ceiling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScriptHeight
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
set_option backward.isDefEq.respectTransparency false

private theorem max_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) : BinaryFn (fun q => max (f q) (g q)) := by
  simpa only [max_def] using BinaryFn.ite (hf.le hg) hg hf

theorem rank_binary {S B : List Bool → ℕ} (hS : UnaryFn S) (hB : UnaryFn B) : BinaryFn (fun q => rank (S q) (B q)) :=
  ((BinaryFn.const 2).powUnary hB).powUnary (hS.add (UnaryFn.const 2))

theorem factor_binary {n S B W D L : List Bool → ℕ} (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B)
    (hW : UnaryFn W) (hD : BinaryFn D) (hL : BinaryFn L) :
    BinaryFn (fun q => coefficientFactor (n q) (S q) (B q) (W q) (D q) (L q)) := by
  have HR := rank_binary hS hB
  have HC := IntegralMixedGlobalHeightBounds.coefficientFactor_binary hn HR hW hD (BinaryFn.ofUnary hS) hL
  have HV := IntegralMixedCutBounds.normalizedHeight_binary HR
    (IntegralMixedCutHeightProfile.factor_binary hn HR hW hD (BinaryFn.ofUnary hS) hL)
  exact (max_binary HC HV).add (BinaryFn.const 1)

theorem growth_binary {n S B W D L : List Bool → ℕ} (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B)
    (hW : UnaryFn W) (hD : BinaryFn D) (hL : BinaryFn L) :
    BinaryFn (fun q => growth (n q) (S q) (B q) (W q) (D q) (L q)) :=
  bankGrowth_binary (rank_binary hS hB) ((BinaryFn.const 2).powUnary hB) (factor_binary hn hS hB hW hD hL)

theorem height_binary {n S B W D L C j : List Bool → ℕ} (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B)
    (hW : UnaryFn W) (hD : BinaryFn D) (hL : BinaryFn L) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => height (n q) (S q) (B q) (W q) (D q) (L q) (C q) (j q)) :=
  ((growth_binary hn hS hB hW hD hL).powUnary hj).mul (hC.add (BinaryFn.const 1))

theorem height_bits (n S B W D L C j : ℕ) :
    (height n S B W D L C j).size ≤ (growth n S B W D L).size * j + (C + 1).size + 1 := by
  have HG : growth n S B W D L ^ j ≤ 2 ^ ((growth n S B W D L).size * j) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left (Nat.lt_size_self (growth n S B W D L)).le j
  have HH : height n S B W D L C j ≤ 2 ^ ((growth n S B W D L).size * j + (C + 1).size) :=
    (Nat.mul_le_mul HG (Nat.lt_size_self (C + 1)).le).trans_eq (pow_add _ _ _).symm
  simpa only [Nat.size_pow] using Nat.size_le_size HH
end LeanCanny.Algebra.IntegralMixedFullScriptHeight
