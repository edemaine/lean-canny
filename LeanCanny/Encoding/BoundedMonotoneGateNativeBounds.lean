/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedMonotoneGateBounds
public import LeanCanny.Encoding.MonotoneGateNativeBounds
/-! # Native original-atom caps for the bounded equation source -/
@[expose] public section
namespace LeanCanny.Encoding.BoundedMonotoneGateSource
open ETR LeanCanny.Computation MonotoneGateSource

def degreeBudget (F : Family) (c : List Bool) : ℕ := 4*max (atomMass F c) 2

theorem degreeBudget_unary (F : Family) (hF : Access F) : UnaryFn (degreeBudget F) :=
  (UnaryFn.const 4).mul ((atomMass_unary F hF).max (UnaryFn.const 2))

theorem polynomial_degree_budget (F : Family) (c : List Bool) :
    (polynomial F c).degreeBound≤degreeBudget F c :=
  polynomial_degree F c (atomMass F c) (atom_degree_mass F c)

theorem polynomial_totalDegree_budget (F : Family) (c : List Bool) :
    (polynomial F c).toPolynomial.totalDegree≤degreeBudget F c :=
  (polynomial F c).totalDegree_toPolynomial_le.trans (polynomial_degree_budget F c)

end LeanCanny.Encoding.BoundedMonotoneGateSource
