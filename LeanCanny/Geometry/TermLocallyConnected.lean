/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialLocallyConnected
public import LeanCanny.Geometry.TermFiniteComponents
/-! # Literal integer term zero sets are complete and locally connected -/
@[expose] public section
namespace LeanCanny.Geometry.TermLocallyConnected
open LeanCanny.ETR

theorem locallyConnected (t : Term) (n : ℕ) : LocallyConnectedSpace (TermFiniteComponents.Zeros t n) := by
  rw [TermFiniteComponents.zero_eq]
  exact PolynomialLocallyConnected.locallyConnected _

theorem complete (t : Term) (n : ℕ) : CompleteSpace (TermFiniteComponents.Zeros t n) := by
  rw [TermFiniteComponents.zero_eq]
  exact (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).isComplete.completeSpace_coe
end LeanCanny.Geometry.TermLocallyConnected
