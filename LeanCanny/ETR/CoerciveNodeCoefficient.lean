/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicFixedTableCoefficientSpace
public import LeanCanny.ETR.CoerciveFormalLeafReader

/-! # Native coefficients at every formal coercive table node -/
@[expose] public section
namespace LeanCanny.ETR.CoerciveNodeCoefficient
open LeanCanny.Computation LeanCanny.Algebra

theorem evaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
    (SymbolicFixedTablePolynomialTree.node CoerciveFormalLeafReader.leaf)) :=
  SymbolicFixedTableTreeSource.coefficientEvaluator CoerciveFormalLeafReader.leaf
    CoerciveFormalLeafReader.bound CoerciveFormalLeafReader.leaf_inner_degree
    CoerciveFormalLeafReader.bound_binary CoerciveFormalLeafReader.leafEvaluator

end LeanCanny.ETR.CoerciveNodeCoefficient
