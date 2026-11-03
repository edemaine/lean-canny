/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareNative
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest
/-! # Original-only access and marked tests for the full physical replay

The literal marked or signed-outer bank supplies its existing original
controls. No full-row evaluator is an input to these factories.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native tables IntegralMixedPhysicalMarkedPlan.controls
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem row_evaluator : SpaceFunction (SquareSampleInput.rowCoefficient
    (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer)) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  exact IntegralFramedPhysicalSquare.native_row_evaluator B.parameters A.parameters B.plan B.data
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    B.nodes B.factor B.seed B.bounds B.key A.key B.positive A.liftedData A.controls A.bounds

theorem access : (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer).Access :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  exact IntegralFramedPhysicalSquare.native_access B.parameters A.parameters B.plan B.data
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    B.nodes B.factor B.seed B.bounds A.nodes A.factor A.seed B.key A.key B.positive A.liftedData A.controls A.bounds

theorem regular_evaluator : SpaceFunction (IntegralMixedPhysicalMarkedTest.regularValue hn ht ha hR outer) :=
  IntegralMixedPhysicalMarkedTest.regular_evaluator hn ht ha hR outer (row_evaluator hn ht ha hR outer)

theorem mark_evaluator : SpaceFunction (IntegralMixedPhysicalMarkedTest.markValue hn ht ha hR outer) :=
  IntegralMixedPhysicalMarkedTest.mark_evaluator hn ht ha hR outer (row_evaluator hn ht ha hR outer)

theorem leaves_decider : SpaceDecider (IntegralMixedPhysicalMarkedTest.leaves hn ht ha hR outer) :=
  IntegralMixedPhysicalMarkedTest.leaves_decider hn ht ha hR outer (row_evaluator hn ht ha hR outer)

theorem decider : SpaceDecider (IntegralMixedPhysicalMarkedTest.language hn ht ha hR outer) :=
  IntegralMixedPhysicalMarkedTest.decider hn ht ha hR outer (row_evaluator hn ht ha hR outer)

end LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
