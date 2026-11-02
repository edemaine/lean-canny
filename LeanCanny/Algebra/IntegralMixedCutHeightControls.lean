/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutHeightEnvelope
public import LeanCanny.Algebra.IntegralMixedGlobalHeightControls
/-! # The uniform raw-cut height factor has original-only binary controls -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutHeightProfile
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
set_option backward.isDefEq.respectTransparency false

private theorem max_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) : BinaryFn (fun q => max (f q) (g q)) := by
  simpa only [max_def] using BinaryFn.ite (hf.le hg) hg hf

theorem input_binary {n S L : List Bool → ℕ} (hn : UnaryFn n) (hS : BinaryFn S) (hL : BinaryFn L) :
    BinaryFn (fun q => input (n q) (S q) (L q)) :=
  ((BinaryFn.ofUnary hn).add (BinaryFn.const 2)).mul (IntegralMixedGlobalHeightBounds.expressionFactor_binary hS hL)

theorem coordinate_binary {n R W D S L : List Bool → ℕ} (hn : UnaryFn n) (hR : BinaryFn R) (hW : UnaryFn W)
    (hD : BinaryFn D) (hS : BinaryFn S) (hL : BinaryFn L) : BinaryFn (fun q => coordinate (n q) (R q) (W q) (D q) (S q) (L q)) :=
  IntegralMixedCoordinateBounds.height_binary hn hR hW hD hS hL (BinaryFn.const 1)

theorem row_binary {n R W D S L : List Bool → ℕ} (hn : UnaryFn n) (hR : BinaryFn R) (hW : UnaryFn W)
    (hD : BinaryFn D) (hS : BinaryFn S) (hL : BinaryFn L) : BinaryFn (fun q => row (n q) (R q) (W q) (D q) (S q) (L q)) := by
  have HT := input_binary hn hS hL
  have HC := IntegralFrozenConstantBounds.lowerHeight_binary (BinaryFn.ofUnary (hn.add (UnaryFn.const 1))) hR hW hD HT HT HT HT
  have HG := IntegralFrozenCoefficientBounds.coefficientHeight_binary (BinaryFn.ofUnary (hn.add (UnaryFn.const 1))) hR hW hD
    (HT.add (BinaryFn.ofUnary hW)) HT HT
  exact (((((HC.add HG).add (HT.add (hD.mul HT))).add (BinaryFn.ofUnary hW)).add
    (BinaryFn.ofUnary (hn.add (UnaryFn.const 1))).size).add (BinaryFn.const 1))

theorem columns_binary {n D : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) : BinaryFn (fun q => columns (n q) (D q)) := by
  have HK := PurePowerReductionBounds.dimension_binary (hn.add (UnaryFn.const 1)) hD
  have HB := (hD.add ((BinaryFn.ofUnary (hn.add (UnaryFn.const 1))).mul HK)).add (BinaryFn.const 1)
  have HW : UnaryFn (fun q => IntegralMixedExceptionalBounds.boxWidth (n q + 1) (D q)) :=
    (UnaryFn.length HB.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((BinaryFn.const 2).powUnary HW).powUnary (hn.add (UnaryFn.const 2))

theorem rows_binary {n D : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) : BinaryFn (fun q => rows (n q) (D q)) :=
  ((BinaryFn.ofUnary hn).add (BinaryFn.const 3)).mul (columns_binary hn hD)

theorem factor_binary {n R W D S L : List Bool → ℕ} (hn : UnaryFn n) (hR : BinaryFn R) (hW : UnaryFn W)
    (hD : BinaryFn D) (hS : BinaryFn S) (hL : BinaryFn L) : BinaryFn (fun q => factor (n q) (R q) (W q) (D q) (S q) (L q)) := by
  have HC := coordinate_binary hn hR hW hD hS hL
  have HR := row_binary hn hR hW hD hS hL
  have HS := (HC.add HR).add (BinaryFn.const 1)
  have HV := IntegralRelativeCharacteristicBounds.determinantHeight_binary (columns_binary hn hD) hR
    (IntegralMacaulayGramBounds.gramHeight_binary (rows_binary hn hD) hR HS)
  have HP := IntegralPrincipalHeightBounds.height_binary (PurePowerReductionBounds.dimension_binary (hn.add (UnaryFn.const 1)) hD) hR HC
  exact max_binary (max_binary HC (max_binary HP HV))
    (IntegralMixedLimitCoordinateBounds.factor_binary hn hR hW hD hS hL)
end LeanCanny.Algebra.IntegralMixedCutHeightProfile
