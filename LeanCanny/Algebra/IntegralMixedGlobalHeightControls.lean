/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGlobalHeightBounds
/-! # Binary controls and logarithmic size of the original-spatial ceiling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGlobalHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
set_option backward.isDefEq.respectTransparency false

theorem height_bits (n M W D N S L C j : ℕ) :
    (height n M W D N S L C j).size ≤ (growth n M W D N S L).size * j + (C + 1).size + 1 := by
  have HG : growth n M W D N S L ^ j ≤ 2 ^ ((growth n M W D N S L).size * j) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left (Nat.lt_size_self (growth n M W D N S L)).le j
  have HH : height n M W D N S L C j ≤ 2 ^ ((growth n M W D N S L).size * j + (C + 1).size) :=
    (Nat.mul_le_mul HG (Nat.lt_size_self (C + 1)).le).trans_eq (pow_add _ _ _).symm
  simpa only [Nat.size_pow] using Nat.size_le_size HH

theorem expressionFactor_binary {S L : List Bool → ℕ} (hS : BinaryFn S) (hL : BinaryFn L) :
    BinaryFn (fun c => expressionFactor (S c) (L c)) :=
  (hL.add (BinaryFn.const 1)).mul (hS.add (BinaryFn.const 3))

theorem coefficientFactor_binary {n M W D S L : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hS : BinaryFn S) (hL : BinaryFn L) :
    BinaryFn (fun c => coefficientFactor (n c) (M c) (W c) (D c) (S c) (L c)) :=
  ((IntegralHistoryGlobalHeightBounds.criticalFactor_binary (hn.add (UnaryFn.const 1)) hM hW hD).mul
    (expressionFactor_binary hS hL)).add (BinaryFn.const 1)

theorem growth_binary {n M W D N S L : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hN : BinaryFn N) (hS : BinaryFn S) (hL : BinaryFn L) :
    BinaryFn (fun c => growth (n c) (M c) (W c) (D c) (N c) (S c) (L c)) :=
  bankGrowth_binary hM hN (coefficientFactor_binary hn hM hW hD hS hL)

theorem height_binary {n M W D N S L C j : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hN : BinaryFn N) (hS : BinaryFn S) (hL : BinaryFn L)
    (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun c => height (n c) (M c) (W c) (D c) (N c) (S c) (L c) (C c) (j c)) :=
  ((growth_binary hn hM hW hD hN hS hL).powUnary hj).mul (hC.add (BinaryFn.const 1))

theorem height_iterate (n M W D N S L C : ℕ) (G : ℕ → ℕ) (h0 : G 0 ≤ C + 1)
    (hs : ∀ j, G (j + 1) ≤ growth n M W D N S L * G j) (j : ℕ) :
    G j ≤ height n M W D N S L C j := by
  induction j with
  | zero => simpa only [height, pow_zero, Nat.one_mul] using h0
  | succ j ih => exact (hs j).trans ((Nat.mul_le_mul_left _ ih).trans_eq (height_step _ _ _ _ _ _ _ _ _).symm)

end LeanCanny.Algebra.IntegralMixedGlobalHeightBounds
