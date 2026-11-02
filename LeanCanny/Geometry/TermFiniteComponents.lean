/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialFiniteComponents
public import LeanCanny.ETR.FinitePolynomial
public import LeanCanny.Algebra.PolynomialMapDegree
/-! # Finite components of literal integer term zero sets, including unbounded sets -/
@[expose] public section
namespace LeanCanny.Geometry.TermFiniteComponents
open Set LeanCanny.ETR MvPolynomial
open scoped Classical
noncomputable def polynomial (t : Term) (n : ℕ) := (t.finitePolynomial n).map (Int.castRingHom ℝ)
noncomputable def Zeros (t : Term) (n : ℕ) := {x : Fin n → ℝ | t.eval (Formula.extend x)=0}

theorem degree (t : Term) (n : ℕ) : (polynomial t n).totalDegree≤t.toData.size :=
  (LeanCanny.Algebra.PolynomialMapDegree.degree_le _ _).trans
    ((Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _))

theorem zero_eq (t : Term) (n : ℕ) : Zeros t n=CoerciveComponentSampling.Zeros (polynomial t n) := by
  ext x
  change t.eval (Formula.extend x)=0 ↔ (polynomial t n).eval x=0
  rw [polynomial,MvPolynomial.eval_map,Term.eval_finitePolynomial]

theorem components_finite (t : Term) (n : ℕ) : Finite (ConnectedComponents (Zeros t n)) := by
  rw [zero_eq]
  exact PolynomialFiniteComponents.components_finite _ t.toData.size (degree t n)
end LeanCanny.Geometry.TermFiniteComponents
