/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedZeroPerturbation
public import LeanCanny.Encoding.GeneralRegularLevel

/-! # Native controls for the bounded zero-source perturbation

All degree and coefficient-mass allowances, the safe tolerance exponent, and
the pure-power perturbation exponent are computed from unary dimension and
binary source degree, mass and radius allowances. This module computes the
controls, not the potentially enormous integer coefficients themselves.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedZeroControls
open LeanCanny.Geometry.BoundedZeroSource

theorem degree_binary {degree : List Bool → ℕ} (hD : BinaryFn degree) :
    BinaryFn (fun c => degreeAllowance (degree c)) :=
  (BinaryFn.const 2).mul (hD.add (BinaryFn.const 2))

theorem powerDegree_binary {degree : List Bool → ℕ} (hD : BinaryFn degree) :
    BinaryFn (fun c => powerDegree (degree c)) :=
  (BinaryFn.const 2).mul (((BinaryFn.const 2).mul (degree_binary hD)).add (BinaryFn.const 1))

theorem massExponent_binary {dim mass radius : List Bool → ℕ}
    (hd : UnaryFn dim) (hb : BinaryFn mass) (hR : BinaryFn radius) :
    BinaryFn (fun c => massExponent (dim c) (mass c) (radius c)) := by
  have hn := (BinaryFn.ofUnary (hd.add (UnaryFn.const 3))).size
  exact (((BinaryFn.const 2).mul hb).add ((BinaryFn.const 2).mul (((BinaryFn.const 2).mul hR).add hn))).add
    (BinaryFn.const 1)

theorem toleranceExponent_binary {dim degree mass radius : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) (hR : BinaryFn radius) :
    BinaryFn (fun c => LeanCanny.Geometry.GeneralCriticalValueBounds.exponent (dim c + 2)
      (degreeAllowance (degree c)) (massExponent (dim c) (mass c) (radius c))) :=
  GeneralRegularLevel.exponent_binary (hd.add (UnaryFn.const 2)) (degree_binary hD) (massExponent_binary hd hb hR)

theorem perturbationExponent_binary {dim degree mass radius : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) (hR : BinaryFn radius) :
    BinaryFn (fun c => perturbationExponent (dim c) (degree c) (mass c) (radius c)) := by
  have hp := (hR.mul (powerDegree_binary hD)).add ((BinaryFn.ofUnary (hd.add (UnaryFn.const 2))).size)
  exact ((toleranceExponent_binary hd hD hb hR).add hp).add (BinaryFn.const 1)

end LeanCanny.Encoding.BoundedZeroControls
