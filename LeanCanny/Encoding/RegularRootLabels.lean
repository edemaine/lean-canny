/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularAffineRootCount
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native preparation of regular-root label widths

The number of roots is exponential in a width computed in polynomial time
from a unary dimension and a binary degree. The degree itself is never
converted to unary.
-/

@[expose] public section
namespace LeanCanny.Encoding.RegularRootLabels
open LeanCanny.Geometry

theorem width_unary {dim degree : List Bool → ℕ} (hn : UnaryFn dim) (hD : BinaryFn degree) :
    UnaryFn (fun c => RegularAffineRootCount.labelWidth (dim c) (degree c)) := by
  have hlevel := ((BinaryFn.ofUnary hn).mul (hD.sub (BinaryFn.const 1))).add (BinaryFn.const 1)
  have hbits : UnaryFn (fun c => (dim c * (degree c - 1) + 1).size) :=
    (UnaryFn.length hlevel.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode _)
  exact (hn.mul (hn.add (UnaryFn.const 1))).mul hbits

end LeanCanny.Encoding.RegularRootLabels
