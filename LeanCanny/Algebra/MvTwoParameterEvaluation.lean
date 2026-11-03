/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvTwoParameterCoefficient
public import LeanCanny.Algebra.RealIteratedTarski
/-! # Ordered formal parameters evaluate at the literal two-head tuple -/
@[expose] public section
namespace LeanCanny.Algebra.MvTwoParameterCoefficient
open Polynomial

variable {m : ℕ} {R : Type*} [CommRing R]

theorem point_evaluate (f : R→+*ℝ) (z : Fin m→ℝ) (p : MvPolynomial (Fin (m+2)) R) (ε δ : ℝ) :
    RealIteratedTarski.evaluate ε δ (evaluate f z p)=p.eval₂ f (Fin.cons δ (Fin.cons ε z)) :=by
  have H : (RealIteratedTarski.evaluate ε δ).comp (evaluate f z)=
      MvPolynomial.eval₂Hom f (Fin.cons δ (Fin.cons ε z)) :=by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evaluate,separate,RealIteratedTarski.evaluate_apply,MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
      all_goals simp [evaluate,separate,RealIteratedTarski.evaluate_apply,MvPolynomial.finSuccEquiv_apply]
      rw [show (1 : Fin (m+2))=(0 : Fin (m+1)).succ from rfl,Fin.cases_succ]
      simp [MvPolynomial.finSuccEquiv_apply]
  exact congrArg (fun φ=>φ p) H

/-- Equality after every ordered real specialization determines the formal head. -/
theorem polynomial_ext (p q : ((ℝ[X])[X])[X])
    (h : ∀ε δ,(p.map (RealIteratedTarski.evaluate ε δ))=(q.map (RealIteratedTarski.evaluate ε δ))) : p=q :=by
  apply Polynomial.ext
  intro y
  apply Polynomial.ext
  intro d
  apply Polynomial.funext
  intro ε
  have H : (p.coeff y).map (Polynomial.evalRingHom ε)=(q.coeff y).map (Polynomial.evalRingHom ε) :=by
    apply Polynomial.funext
    intro δ
    have HC:=congrArg (fun a : ℝ[X]=>a.coeff y) (h ε δ)
    simpa only [Polynomial.coeff_map,RealIteratedTarski.evaluate_apply,Polynomial.eval_map] using HC
  have HC:=congrArg (fun a : ℝ[X]=>a.coeff d) H
  simpa only [Polynomial.coeff_map,Polynomial.coe_evalRingHom] using HC

end LeanCanny.Algebra.MvTwoParameterCoefficient
