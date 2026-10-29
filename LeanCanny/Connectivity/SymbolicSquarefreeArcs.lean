/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SymbolicUnivariateRootFamily
public import LeanCanny.Connectivity.OriginalRootArcs
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Complete arcs for repeated symbolic univariate roots

Squarefree preprocessing gives regular auxiliary branches away from its
explicit exceptional polynomial. Properness and endpoint equations remain
those of the original repeated polynomial.
-/

@[expose] public section
namespace LeanCanny.Connectivity.SymbolicSquarefreeArcs
open Set Geometry LeanCanny.Algebra
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma eval_swap (Q : Polynomial (Polynomial ℝ)) (t x : ℝ) :
    (Polynomial.Bivariate.swap Q).eval₂ (Polynomial.evalRingHom x) t = Q.eval₂ (Polynomial.evalRingHom t) x := by
  have he : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℝ := by
    ext a; simp
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | monomial n a =>
    simp [Polynomial.Bivariate.swap_monomial, Polynomial.eval₂_map, he, Polynomial.eval₂_pow, Polynomial.eval₂_C]

noncomputable def limitPolynomial (p : Polynomial Coefficient) : Polynomial (Polynomial ℝ) :=
  Polynomial.Bivariate.swap (SymbolicUnivariateRootFamily.realPolynomial p)

lemma limitPolynomial_ne_zero (p : Polynomial Coefficient) (hp : p ≠ 0) : limitPolynomial p ≠ 0 :=
  (Polynomial.Bivariate.swap.map_ne_zero_iff).mpr (SymbolicUnivariateRootFamily.realPolynomial_ne_zero p hp)

lemma limit_relation (p : Polynomial Coefficient) (t x : ℝ) :
    AlgebraicBranchLimit.value (limitPolynomial p) t x = p.eval₂ (scalarEvaluation t) x := by
  rw [AlgebraicBranchLimit.value, limitPolynomial, eval_swap,
    SymbolicUnivariateRootFamily.realPolynomial, Polynomial.eval₂_map, SymbolicUnivariateRootFamily.evaluation_comp]

noncomputable abbrev auxiliary (p : Polynomial Coefficient) :=
  SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p)

/-- Multiplicities in the original equation require no Jacobian assumption.
The finite exceptional set is controlled by the explicit integer factor. -/
theorem exists_anchored_arcs (p : Polynomial Coefficient) (hp : p ≠ 0)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional p) ≠ 0)
    (hproper : IsProperMap (RootProjection.projection (SymbolicUnivariateRootFamily.value p))) :
    Finite (RootBranches.Index (auxiliary p) a b t₀) ∧
    ∃ curve : RootBranches.Index (auxiliary p) a b t₀ → ℝ → Fin 1 → ℝ,
      (∀ j, curve j t₀.val = j.val.val.val.2) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → SymbolicUnivariateRootFamily.value p (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, SymbolicUnivariateRootFamily.value p (t.val, x) = 0 ↔ ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  apply OriginalRootArcs.exists_anchored_arcs (SymbolicUnivariateRootFamily.value p) (auxiliary p) a b t₀
    (p := fun _ => limitPolynomial p)
  · intro t ht x
    exact SymbolicUnivariateRootFamily.roots_away p t x (havoid t ht)
  · exact (SymbolicUnivariateRootFamily.contDiff_value p 1).continuous
  · exact hproper
  · intro z _
    exact (SymbolicUnivariateRootFamily.contDiff_value (SymbolicScaledSquarefree.polynomial p) 1).contDiffAt
  · intro z hz
    exact SymbolicUnivariateRootFamily.regular_away p z.val.1 z.val.2 (havoid _ hz) z.property
  · intro _
    exact limitPolynomial_ne_zero p hp
  · intro z _ i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [limit_relation]
    exact (SymbolicUnivariateRootFamily.value_zero_iff p z.val.1 z.val.2).mp z.property

end LeanCanny.Connectivity.SymbolicSquarefreeArcs
