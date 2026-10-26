/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedRegularSource
public import LeanCanny.Encoding.BoundedZeroControls
public import LeanCanny.Encoding.CriticalRegularLevel

/-! # Native controls for the shifted regular source

The second regularization exponent is computed from the actual shifted
source's derived mass bound. All controls remain native polynomial time in
the original binary allowances and unary dimension.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularControls
open LeanCanny.Geometry
open BoundedZeroSource BoundedRegularSource

theorem sourceMassExponent_binary {dim degree mass radius : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) (hR : BinaryFn radius) :
    BinaryFn (fun c => sourceMassExponent (dim c) (degree c) (mass c) (radius c)) := by
  have hF := BoundedZeroControls.perturbationExponent_binary hd hD hb hR
  have hp := (hR.mul (BoundedZeroControls.powerDegree_binary hD)).add
    ((BinaryFn.ofUnary (hd.add (UnaryFn.const 2))).size)
  have hl := ((hF.add (BoundedZeroControls.massExponent_binary hd hb hR)).add hp).add (BinaryFn.const 1)
  exact hl.add ((BinaryFn.ofUnary (hd.add (UnaryFn.const 5))).size)

theorem regularizationExponent_binary {dim degree mass radius : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) (hR : BinaryFn radius) :
    BinaryFn (fun c => regularizationExponent (dim c) (degree c) (mass c) (radius c)) :=
  CriticalRegularLevel.exponent_binary (hd.add (UnaryFn.const 3)) (BoundedZeroControls.powerDegree_binary hD)
    (sourceMassExponent_binary hd hD hb hR)

end LeanCanny.Encoding.BoundedRegularControls
