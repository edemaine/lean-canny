/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicSquarefreeExceptional
public import LeanCanny.Geometry.UnivariateRootFamily
public import LeanCanny.Geometry.AlgebraicBranchLimit
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Root-preserving regular coordinate families

Squarefree preprocessing of integer coordinate equations gives an analytic
regular system away from explicitly constructed exceptional polynomials.
The original equations supply nonzero algebraic relations for endpoint limits.
No equality of original and auxiliary endpoint fibers is asserted.
-/

@[expose] public section
namespace LeanCanny.Geometry.SquarefreeRootFamily
open LeanCanny.Algebra Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def realPolynomial (p : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℝ) :=
  p.map (Polynomial.mapRingHom (Int.castRingHom ℝ))

lemma specialize (p : Polynomial (Polynomial ℤ)) (t : ℝ) :
    (realPolynomial p).map (Polynomial.evalRingHom t) =
      p.map (SymbolicScaledSquarefree.scalarEvaluation t) := by
  rw [realPolynomial, Polynomial.map_map]
  congr 1
  ext <;> simp [SymbolicScaledSquarefree.scalarEvaluation]

lemma eval_realPolynomial (p : Polynomial (Polynomial ℤ)) (t x : ℝ) :
    (realPolynomial p).eval₂ (Polynomial.evalRingHom t) x =
      p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) x := by
  rw [← Polynomial.eval_map, specialize, Polynomial.eval_map]

lemma realPolynomial_ne_zero {p : Polynomial (Polynomial ℤ)} (hp : p ≠ 0) :
    realPolynomial p ≠ 0 :=
  (Polynomial.map_ne_zero_iff
    (Polynomial.map_injective _ (Int.cast_injective (α := ℝ)))).mpr hp

/-- Put the parameter outermost, as required by the branch-limit theorem. -/
noncomputable def endpointEquation (p : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℝ) :=
  Polynomial.Bivariate.swap (realPolynomial p)

lemma endpointEquation_ne_zero {p : Polynomial (Polynomial ℤ)} (hp : p ≠ 0) :
    endpointEquation p ≠ 0 := by
  intro hz
  apply realPolynomial_ne_zero hp
  exact Polynomial.Bivariate.swap.injective (hz.trans (map_zero _).symm)

lemma value_endpointEquation (p : Polynomial (Polynomial ℤ)) (t x : ℝ) :
    AlgebraicBranchLimit.value (endpointEquation p) t x =
      p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) x := by
  have h := Polynomial.Bivariate.aevalAeval_swap x t (realPolynomial p)
  simp only [Polynomial.coe_aevalAeval_eq_evalEval] at h
  change (endpointEquation p).eval₂ (Polynomial.evalRingHom x) t = _
  rw [endpointEquation, Polynomial.eval₂_evalRingHom, h, ← Polynomial.eval₂_evalRingHom]
  exact eval_realPolynomial p t x

variable {ι : Type*}

noncomputable def rows (p : ι → Polynomial (Polynomial ℤ)) :
    ι → MvPolynomial ι (Polynomial ℝ) :=
  UnivariateRootFamily.diagonal (fun i => realPolynomial (p i))

noncomputable def value (p : ι → Polynomial (Polynomial ℤ)) : ℝ × (ι → ℝ) → ι → ℝ :=
  PolynomialRootFamily.value (rows p)

lemma value_apply (p : ι → Polynomial (Polynomial ℤ)) (t : ℝ) (x : ι → ℝ) (i : ι) :
    value p (t, x) i = (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) (x i) :=
  (UnivariateRootFamily.value_diagonal _ t x i).trans (eval_realPolynomial (p i) t (x i))

variable [Fintype ι]

lemma continuous_value (p : ι → Polynomial (Polynomial ℤ)) : Continuous (value p) :=
  (PolynomialRootFamily.contDiff_value (rows p) 1).continuous

omit [Fintype ι] in
lemma roots_away (p : ι → Polynomial (Polynomial ℤ)) (t : ℝ) (x : ι → ℝ)
    (ht : ∀ i, SymbolicScaledSquarefree.scalarEvaluation t
      (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0) :
    value (fun i => SymbolicScaledSquarefree.polynomial (p i)) (t, x) = 0 ↔
      value p (t, x) = 0 := by
  constructor <;> intro hx <;> ext i
  · rw [value_apply]
    exact (SymbolicScaledSquarefree.roots_away (p i) t (x i) (ht i)).mp (by
      simpa only [value_apply, Pi.zero_apply] using congrFun hx i)
  · rw [value_apply]
    exact (SymbolicScaledSquarefree.roots_away (p i) t (x i) (ht i)).mpr (by
      simpa only [value_apply, Pi.zero_apply] using congrFun hx i)

variable [DecidableEq ι]

lemma regular_away (p : ι → Polynomial (Polynomial ℤ)) (t : ℝ) (x : ι → ℝ)
    (ht : ∀ i, SymbolicScaledSquarefree.scalarEvaluation t
      (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0)
    (hx : value (fun i => SymbolicScaledSquarefree.polynomial (p i)) (t, x) = 0) :
    (fderiv ℝ (value (fun i => SymbolicScaledSquarefree.polynomial (p i))) (t, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible := by
  apply UnivariateRootFamily.regular_diagonal _ t x _ hx
  intro i
  rw [specialize]
  exact SymbolicScaledSquarefree.separable_away (p i) t (ht i)

omit [DecidableEq ι] in
/-- The excluded parameter set is finite, even when original fibers have
repeated roots identically in the parameter. -/
lemma finite_exceptional (p : ι → Polynomial (Polynomial ℤ)) (hp : ∀ i, p i ≠ 0) :
    {t : ℝ | ∃ i, SymbolicScaledSquarefree.scalarEvaluation t
      (SymbolicScaledSquarefree.exceptional (p i)) = 0}.Finite := by
  have h := Set.finite_iUnion (fun i => SymbolicScaledSquarefree.finite_exceptional (p i) (hp i))
  exact h.subset (fun _ ht => Set.mem_iUnion.mpr ht)

end LeanCanny.Geometry.SquarefreeRootFamily
