/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Evaluating a univariate polynomial after multivariate substitution -/

public section

namespace LeanCanny.CountingHierarchy

variable {ι R : Type*} [CommRing R]

theorem eval_map_polynomial_aeval (point : ι → R) (v : MvPolynomial ι ℤ) (g : Polynomial ℤ) :
    MvPolynomial.eval point ((Polynomial.aeval v g).map (Int.castRingHom R)) =
      g.eval₂ (Int.castRingHom R) (MvPolynomial.eval point (v.map (Int.castRingHom R))) := by
  let ψ : MvPolynomial ι ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) point
  have h := Polynomial.map_aeval_eq_aeval_map (φ := Int.castRingHom R) (ψ := ψ)
    (by ext a; simp [ψ]) g v
  rw [MvPolynomial.eval_map]
  change ψ (Polynomial.aeval v g) = _
  rw [h]
  simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, MvPolynomial.eval_map]
  rfl

end LeanCanny.CountingHierarchy
