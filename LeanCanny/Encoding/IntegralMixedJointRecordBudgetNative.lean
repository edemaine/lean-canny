/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointGeneralSlabBounds
/-! # Original-only native unary bounds for the actual three-record slab word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCutRecordConstructor
open LeanCanny.Algebra

theorem codeBudget_unary {n birth B : List Bool→ℕ} (hn : UnaryFn n) (hm : BinaryFn birth)
    (hB : UnaryFn B) : UnaryFn (fun q=>codeBudget (n q) (birth q) (B q)) :=by
  have HM : UnaryFn (fun q=>(birth q).size):=
    (UnaryFn.length hm.bits_mem_FP).of_eq (fun q=>BinaryNatCode.length_encode (birth q))
  have HN : UnaryFn (fun q=>(n q+1).size):=
    (UnaryFn.length ((BinaryFn.ofUnary hn).add (BinaryFn.const 1)).bits_mem_FP).of_eq
      (fun q=>BinaryNatCode.length_encode (n q+1))
  have HR:=((UnaryFn.const 3).mul HM).add (UnaryFn.const 18)
  have HT:=(((UnaryFn.const 2).mul HR).add (UnaryFn.const 2)).mul (hn.add (UnaryFn.const 1))
  have HF:=((HT.add HN).add hB).add (UnaryFn.const 5)
  exact (((UnaryFn.const 2).mul HF).add (UnaryFn.const 2)).mul (UnaryFn.const 16)

end LeanCanny.Encoding.IntegralMixedCutRecordConstructor

namespace LeanCanny.Geometry.IntegralMixedFrozenFrame

theorem jointSlabByteBudget_unary {n birth B : List Bool→ℕ} (hn : UnaryFn n) (hm : BinaryFn birth)
    (hB : UnaryFn B) : UnaryFn (fun q=>jointSlabByteBudget (n q) (birth q) (B q)) :=by
  have H0:=Encoding.IntegralMixedCutRecordConstructor.codeBudget_unary hn hm hB
  have H1:=Encoding.IntegralMixedCutRecordConstructor.codeBudget_unary hn (hm.add (BinaryFn.const 1)) hB
  have H2:=Encoding.IntegralMixedCutRecordConstructor.codeBudget_unary hn (hm.add (BinaryFn.const 2)) hB
  exact (((UnaryFn.const 2).mul ((H0.add H1).add H2)).add (UnaryFn.const 2)).mul (UnaryFn.const 3)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
