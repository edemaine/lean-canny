/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateHeightRecordSemantics
public import LeanCanny.Algebra.IntegralMixedFiniteHeight
public import LeanCanny.Algebra.IntegralMixedHistorySemantics

/-! # Actual coordinate-height records in a retained mixed bank

The copied-height and midpoint records used by the trace factories match
the finite mixed-height fragment exactly. The correlation guards name the
actual retained quotients and ancestral coordinates. Common-denominator
clearing preserves the resulting real slice equation.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateHeightMixedBank
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedFiniteHeight
open scoped Classical
variable {n S B m a k : ℕ} {P : SpatialSource n} {ι : Type}

theorem height_value (x : State P S B m ι)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (reference : Fin m)
    (index : Fin a) (ancestor : Fin k) (z : FlatAffineCriticalTower.Ancestors a k → ℝ)
    (hvalue : φ (x.bank.numerator reference) / (x.bank.denominator reference : ℝ) =
      z (FlatAffineCriticalTower.oldAmbient k ancestor index)) :
    φ (expression x (Level.height reference.val).expression) = (commonDenominator x : ℝ) *
      (FlatAffineLevelRecordData.decode a 2 k
        (FlatAffineLevelRecordData.data (CoordinateHeightRecord.height a index.val ancestor.val))).polynomial.eval₂
          (Int.castRingHom ℝ) z := by
  have HE := expression_recover x φ
    (fun i => φ (x.bank.numerator i) / (x.bank.denominator i : ℝ)) (fun _ => rfl)
    (Level.height reference.val).expression
  rw [CoordinateHeightRecord.eval_height]
  have HT : φ (expression x (Level.height reference.val).expression) =
      (commonDenominator x : ℝ) * (2 * (φ (x.bank.numerator reference) / (x.bank.denominator reference : ℝ))) := by
    simpa only [Level.expression, AffineExpr.evaluate, dite_eq_left reference.isLt, Int.cast_ofNat] using HE
  exact HT.trans (congrArg (fun t => (commonDenominator x : ℝ) * (2 * t)) hvalue)

theorem midpoint_value (x : State P S B m ι)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (leftReference rightReference : Fin m)
    (index : Fin a) (left right : Fin k) (z : FlatAffineCriticalTower.Ancestors a k → ℝ)
    (hleft : φ (x.bank.numerator leftReference) / (x.bank.denominator leftReference : ℝ) =
      z (FlatAffineCriticalTower.oldAmbient k left index))
    (hright : φ (x.bank.numerator rightReference) / (x.bank.denominator rightReference : ℝ) =
      z (FlatAffineCriticalTower.oldAmbient k right index)) :
    φ (expression x (Level.midpoint leftReference.val rightReference.val).expression) = (commonDenominator x : ℝ) *
      (FlatAffineLevelRecordData.decode a 2 k
        (FlatAffineLevelRecordData.data (CoordinateHeightRecord.midpoint a index.val left.val right.val))).polynomial.eval₂
          (Int.castRingHom ℝ) z := by
  have HE := expression_recover x φ
    (fun i => φ (x.bank.numerator i) / (x.bank.denominator i : ℝ)) (fun _ => rfl)
    (Level.midpoint leftReference.val rightReference.val).expression
  rw [CoordinateHeightRecord.eval_midpoint]
  have HT : φ (expression x (Level.midpoint leftReference.val rightReference.val).expression) =
      (commonDenominator x : ℝ) * (φ (x.bank.numerator leftReference) / (x.bank.denominator leftReference : ℝ) +
        φ (x.bank.numerator rightReference) / (x.bank.denominator rightReference : ℝ)) := by
    simpa only [Level.expression, AffineExpr.evaluate, dite_eq_left leftReference.isLt,
      dite_eq_left rightReference.isLt] using HE
  rw [hleft, hright] at HT
  exact HT

theorem height_slice (x : State P S B m ι)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (reference : Fin m) (t y : ℝ)
    (hvalue : φ (x.bank.numerator reference) / (x.bank.denominator reference : ℝ) = t) :
    ((2 * commonDenominator x : ℤ) : ℝ) * y = φ (expression x (Level.height reference.val).expression) ↔ y = t := by
  have HE := expression_recover x φ
    (fun i => φ (x.bank.numerator i) / (x.bank.denominator i : ℝ)) (fun _ => rfl)
    (Level.height reference.val).expression
  simp only [Level.expression, AffineExpr.evaluate, dite_eq_left reference.isLt, Int.cast_ofNat] at HE
  dsimp only [Level.expression]
  rw [HE, hvalue, Int.cast_mul, Int.cast_ofNat]
  have HQ : (commonDenominator x : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  constructor
  · intro H
    have HM : (commonDenominator x : ℝ) * (2 * y) = (commonDenominator x : ℝ) * (2 * t) := by nlinarith [H]
    have H2 := mul_left_cancel₀ HQ HM
    linarith
  · intro H
    rw [H]
    ring

end LeanCanny.Encoding.CoordinateHeightMixedBank
