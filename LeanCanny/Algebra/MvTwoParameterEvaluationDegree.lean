/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvTwoParameterCoefficient
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
/-! # One whole-output box bounds both selected infinitesimal scans -/
@[expose] public section
namespace LeanCanny.Algebra.MvTwoParameterCoefficient
open Polynomial
variable {m : ℕ} {R K : Type*} [CommSemiring R] [CommSemiring K]

theorem evaluate_degree (f : R→+*K) (z : Fin m→K) (p : MvPolynomial (Fin (m+2)) R) :
    (evaluate f z p).natDegree≤p.totalDegree :=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro δ hδ
  apply Polynomial.ext
  intro ε
  rw [selected_coefficient,eq_zero p δ ε (Or.inl hδ),MvPolynomial.eval₂_zero,Polynomial.coeff_zero]

theorem evaluate_coefficient_degree (f : R→+*K) (z : Fin m→K) (p : MvPolynomial (Fin (m+2)) R) (δ : ℕ) :
    ((evaluate f z p).coeff δ).natDegree≤p.totalDegree :=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro ε hε
  rw [selected_coefficient,eq_zero p δ ε (Or.inr hε),MvPolynomial.eval₂_zero]

end LeanCanny.Algebra.MvTwoParameterCoefficient
