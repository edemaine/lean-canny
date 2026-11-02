/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateBounds
public import LeanCanny.Algebra.IntegralMixedNormalizedHeightBounds
public import LeanCanny.Algebra.IntegralMixedCutHeightControls

/-! # One original profile includes legacy and limit-coordinate cuts

The additional denominator powers enlarge the raw factor explicitly. The
existing profile is dominated, so every currently interpreted command remains
covered while a new relative tag is introduced independently.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitHeightProfile
open LeanCanny.Encoding FixedWidthPolynomial UniformIntegralPrefix IntegralMixedHistory

def factor (n R W D S L : ℕ) : ℕ := max
  (IntegralMixedCutHeightProfile.factor n R W D S L)
  (IntegralMixedLimitCoordinateBounds.factor n R W D S L)

theorem legacy_factor_le (n R W D S L : ℕ) : IntegralMixedCutHeightProfile.factor n R W D S L ≤ factor n R W D S L := le_max_left _ _
theorem limit_factor_le (n R W D S L : ℕ) : IntegralMixedLimitCoordinateBounds.factor n R W D S L ≤ factor n R W D S L := le_max_right _ _

theorem factor_binary {n R W D S L : List Bool → ℕ} (hn : UnaryFn n) (hR : BinaryFn R) (hW : UnaryFn W)
    (hD : BinaryFn D) (hS : BinaryFn S) (hL : BinaryFn L) : BinaryFn (fun q => factor (n q) (R q) (W q) (D q) (S q) (L q)) := by
  have HA := IntegralMixedCutHeightProfile.factor_binary hn hR hW hD hS hL
  have HB := IntegralMixedLimitCoordinateBounds.factor_binary hn hR hW hD hS hL
  simpa only [factor,max_def] using BinaryFn.ite (HA.le HB) HB HA

def rank (S B : ℕ) := count (S+2) B
def cutFactor (n S B W D L : ℕ) := IntegralMixedCutBounds.normalizedHeight (rank S B) (factor n (rank S B) W D S L)
def coefficientFactor (n S B W D L : ℕ) :=
  max (IntegralMixedGlobalHeightBounds.coefficientFactor n (rank S B) W D S L) (cutFactor n S B W D L)+1
def growth (n S B W D L : ℕ) := bankGrowth (rank S B) (2^B) (coefficientFactor n S B W D L)


theorem cut_growth_le (n S B W D L : ℕ) : bankGrowth (rank S B) (2^B) (cutFactor n S B W D L) ≤ growth n S B W D L := by
  have H : cutFactor n S B W D L ≤ coefficientFactor n S B W D L := (le_max_right _ _).trans (Nat.le_succ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right H 1)) 1

theorem rank_binary {S B : List Bool → ℕ} (hS : UnaryFn S) (hB : UnaryFn B) :
    BinaryFn (fun q => rank (S q) (B q)) :=
  ((BinaryFn.const 2).powUnary hB).powUnary (hS.add (UnaryFn.const 2))

theorem coefficientFactor_binary {n S B W D L : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W) (hD : BinaryFn D) (hL : BinaryFn L) :
    BinaryFn (fun q => coefficientFactor (n q) (S q) (B q) (W q) (D q) (L q)) := by
  have HR := rank_binary hS hB
  have HA := IntegralMixedGlobalHeightBounds.coefficientFactor_binary hn HR hW hD (BinaryFn.ofUnary hS) hL
  have HB := IntegralMixedCutBounds.normalizedHeight_binary HR (factor_binary hn HR hW hD (BinaryFn.ofUnary hS) hL)
  have HM := BinaryFn.ite (HA.le HB) HB HA
  simpa only [max_def,coefficientFactor,cutFactor] using HM.add (BinaryFn.const 1)

theorem growth_binary {n S B W D L : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W) (hD : BinaryFn D) (hL : BinaryFn L) :
    BinaryFn (fun q => growth (n q) (S q) (B q) (W q) (D q) (L q)) :=
  bankGrowth_binary (rank_binary hS hB) ((BinaryFn.const 2).powUnary hB)
    (coefficientFactor_binary hn hS hB hW hD hL)

def height (n S B W D L C j : ℕ) := growth n S B W D L^j*(C+1)

theorem height_binary {n S B W D L C j : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => height (n q) (S q) (B q) (W q) (D q) (L q) (C q) (j q)) :=
  ((growth_binary hn hS hB hW hD hL).powUnary hj).mul (hC.add (BinaryFn.const 1))

theorem growth_pos (n S B W D L : ℕ) : 1 ≤ growth n S B W D L := bankGrowth_pos _ _ _

theorem source_le_height (n S B W D L C j : ℕ) : C+1 ≤ height n S B W D L C j := by
  have H : 1 ≤ growth n S B W D L^j := Nat.one_le_pow _ _ (growth_pos n S B W D L)
  simpa only [height,Nat.one_mul] using Nat.mul_le_mul_right (C+1) H

theorem height_step (n S B W D L C j : ℕ) :
    height n S B W D L C (j+1)=growth n S B W D L*height n S B W D L C j := by
  unfold height
  rw [pow_succ']
  exact Nat.mul_assoc _ _ _

end LeanCanny.Algebra.IntegralMixedLimitHeightProfile
