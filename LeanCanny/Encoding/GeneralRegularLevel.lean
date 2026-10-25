/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.GeneralCriticalValueBounds
public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Native dyadic regularity controls for arbitrary integer polynomials

Unary dimension and binary degree and mass allowances compute the exact
exponent of the general critical-value gap in native polynomial time. Its
potentially enormous denominator is never expanded into an integer literal.
-/

@[expose] public section
namespace LeanCanny.Encoding.GeneralRegularLevel
open LeanCanny.Algebra LeanCanny.Geometry
open CoerciveCriticalHomogenization CoerciveCoordinateEliminant CoerciveRadiusBits
open scoped BigOperators

private theorem macaulay_level (n D : ℕ) : Macaulay.level (finDegree (n := n) D) = n * (2 * D) + 1 := by
  unfold Macaulay.level
  have hs := Equiv.sum_comp (layout (n := n)) (fun j => finDegree D j - 1)
  rw [← hs]
  simp [finDegree, nativeDegree, Fintype.sum_option]

theorem radiusWidth_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hD : BinaryFn degree) :
    UnaryFn (fun c => width (dim c) (degree c)) := by
  have hn := BinaryFn.ofUnary hd
  have hL := (hn.mul ((BinaryFn.const 2).mul hD)).add (BinaryFn.const 1)
  have hP := ((BinaryFn.const 2).mul hD).add (BinaryFn.const 1)
  have hm : BinaryFn (fun c => max (dim c * (2 * degree c) + 1) (2 * degree c + 1)) :=
    (BinaryFn.ite (hL.le hP) hP hL).of_eq (fun _ => by simp only [max_def])
  exact (UnaryFn.length hm.bits_mem_FP).of_eq (fun c => by
    rw [BinaryNatCode.length_encode, width, macaulay_level])

theorem radiusColumnExponent_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hD : BinaryFn degree) :
    UnaryFn (fun c => columnExponent (dim c) (degree c)) :=
  (hd.add (UnaryFn.const 1)).mul (radiusWidth_unary hd hD)

theorem radiusMassExponent_binary {dim degree mass : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) :
    BinaryFn (fun c => CoerciveRadiusBits.massExponent (dim c) (degree c) (mass c)) := by
  have hL := radiusColumnExponent_unary hd hD
  have hC : BinaryFn (fun c => CoerciveCoordinateEliminant.columnBound (dim c) (degree c)) :=
    ((BinaryFn.const 2).powUnary hL).of_eq (fun c => (columnBound_eq (dim c) (degree c)).symm)
  have hB := (hD.size.add ((BinaryFn.const 2).mul hb)).add (BinaryFn.const 3)
  exact (hC.mul ((BinaryFn.ofUnary hL).add hB)).add (BinaryFn.const 1)

theorem exponent_binary {dim degree mass : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) :
    BinaryFn (fun c => GeneralCriticalValueBounds.exponent (dim c) (degree c) (mass c)) := by
  have hB := ((BinaryFn.ofUnary (hd.add (UnaryFn.const 1))).size).add
    ((BinaryFn.const 2).mul ((hb.add hD.size).add (BinaryFn.const 1)))
  exact (radiusMassExponent_binary (hd.add (UnaryFn.const 1)) ((BinaryFn.const 2).mul hD) hB).add
    (BinaryFn.const 1)

end LeanCanny.Encoding.GeneralRegularLevel
