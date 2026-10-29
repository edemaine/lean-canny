/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicSquarefreeExceptional
public import LeanCanny.Geometry.UnivariateRootFamily

/-! # Regular auxiliary families preserving repeated symbolic roots

An explicit exceptional polynomial controls specialization of the symbolic
squarefree quotient. Away from its roots the auxiliary spatial derivative
is invertible, while the original roots are retained without multiplicities.
-/

@[expose] public section
namespace LeanCanny.Geometry.SymbolicUnivariateRootFamily
open LeanCanny.Algebra MvPolynomial
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def realPolynomial (p : Polynomial Coefficient) : Polynomial (Polynomial ℝ) :=
  p.map (Polynomial.mapRingHom (Int.castRingHom ℝ))

noncomputable def value (p : Polynomial Coefficient) : ℝ × (Fin 1 → ℝ) → Fin 1 → ℝ :=
  PolynomialRootFamily.value (UnivariateRootFamily.rows (realPolynomial p))

lemma evaluation_comp (t : ℝ) :
    (Polynomial.evalRingHom t).comp (Polynomial.mapRingHom (Int.castRingHom ℝ)) = scalarEvaluation t := by
  ext <;> simp [scalarEvaluation]

lemma value_eq (p : Polynomial Coefficient) (t : ℝ) (x : Fin 1 → ℝ) (i : Fin 1) :
    value p (t, x) i = p.eval₂ (scalarEvaluation t) (x 0) := by
  change ((realPolynomial p).toMvPolynomial (0 : Fin 1)).eval₂ (Polynomial.evalRingHom t) x = _
  rw [UnivariateRootFamily.eval, realPolynomial, Polynomial.eval₂_map, evaluation_comp]

lemma value_zero_iff (p : Polynomial Coefficient) (t : ℝ) (x : Fin 1 → ℝ) :
    value p (t, x) = 0 ↔ p.eval₂ (scalarEvaluation t) (x 0) = 0 := by
  constructor
  · intro h
    simpa only [value_eq, Pi.zero_apply] using congrFun h 0
  · intro h
    funext i
    exact (value_eq p t x i).trans h

lemma roots_away (p : Polynomial Coefficient) (t : ℝ) (x : Fin 1 → ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) :
    value p (t, x) = 0 ↔ value (SymbolicScaledSquarefree.polynomial p) (t, x) = 0 := by
  rw [value_zero_iff, value_zero_iff]
  exact (SymbolicScaledSquarefree.roots_away p t (x 0) ht).symm

lemma regular_away (p : Polynomial Coefficient) (t : ℝ) (x : Fin 1 → ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0)
    (hx : value (SymbolicScaledSquarefree.polynomial p) (t, x) = 0) :
    (fderiv ℝ (value (SymbolicScaledSquarefree.polynomial p)) (t, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin 1 → ℝ)).IsInvertible := by
  apply UnivariateRootFamily.regular _ t x ?_ hx
  have H : (realPolynomial (SymbolicScaledSquarefree.polynomial p)).map (Polynomial.evalRingHom t) =
      (SymbolicScaledSquarefree.polynomial p).map (scalarEvaluation t) := by
    rw [realPolynomial, Polynomial.map_map, evaluation_comp]
  rw [H]
  exact SymbolicScaledSquarefree.separable_away p t ht

lemma contDiff_value (p : Polynomial Coefficient) (n : WithTop ℕ∞) : ContDiff ℝ n (value p) :=
  PolynomialRootFamily.contDiff_value _ n

lemma realPolynomial_ne_zero (p : Polynomial Coefficient) (hp : p ≠ 0) : realPolynomial p ≠ 0 := by
  apply (Polynomial.map_ne_zero_iff ?_).mpr hp
  exact Polynomial.map_injective (Int.castRingHom ℝ) (Int.cast_injective (α := ℝ))

end LeanCanny.Geometry.SymbolicUnivariateRootFamily
