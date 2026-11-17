/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SeparatedCriticalPolynomial
public import LeanCanny.CountingHierarchy.CoerciveMinimumValue
public import LeanCanny.CountingHierarchy.QuotientEvaluation
public import LeanCanny.Geometry.PolynomialCalculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Coercive minima are roots of the actual critical-value polynomial -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Set
open PurePowerResidue
open scoped Classical Topology

variable {n : ℕ}

/-- The pointwise objective, written in the parameter-affine form used
 by the compact-sublevel minimum theorem. -/
@[expose] noncomputable def criticalObjective (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) (x : Fin n → ℝ) : ℝ :=
  separatedPotential ell a x + u * ((ell + 1 : ℕ) * eval x F)

theorem criticalObjective_eq_eval (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) (x : Fin n → ℝ) :
    criticalObjective ell a F u x = eval x (deformedPolynomial ell a u F) := by
  rw [eval_deformedPolynomial, criticalObjective]
  ring

theorem exists_critical_minimizer (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hFn : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) :
    ∃ x : Fin n → ℝ, IsMinOn (criticalObjective ell a F u) univ x := by
  apply exists_minimizer_of_compact_sublevels
    (fun x => (ell + 1 : ℕ) * eval x F) (separatedPotential ell a)
    (continuous_const.mul (MvPolynomial.continuous_eval F))
    (continuous_separatedPotential ell a) (fun x => mul_nonneg (by positivity) (hFn x))
    (separatedPotential_compact_sublevel ell hell he a ha) (fun _ => 0) u hu

theorem critical_equations_of_minimizer (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) (x : Fin n → ℝ)
    (hx : IsMinOn (criticalObjective ell a F u) univ x) :
    ∀ i, MvPolynomial.aeval x (criticalLower ell a u F i) = x i ^ ell := by
  have hmin : IsMinOn (fun y => eval y (deformedPolynomial ell a u F)) univ x := by
    have heq : criticalObjective ell a F u =
        (fun y => eval y (deformedPolynomial ell a u F)) :=
      funext (criticalObjective_eq_eval ell a F u)
    rwa [← heq]
  have hlocal := hmin.isLocalMin Filter.univ_mem
  have hc := (LeanCanny.Geometry.PolynomialCalculus.critical_iff (RingHom.id ℝ)
    (deformedPolynomial ell a u F) x).mp hlocal.fderiv_eq_zero
  intro i
  have hi := hc i
  rw [pderiv_deformedPolynomial, eval₂_id, map_mul, eval_C] at hi
  have hm : ((ell + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ell
  have hz := (mul_eq_zero.mp hi).resolve_left hm
  rw [map_sub, map_pow, eval_X, sub_eq_zero] at hz
  simpa only [MvPolynomial.aeval_eq_eval] using hz.symm

/-- The minimum value is a root of the concrete quotient characteristic
 polynomial, without a supplied critical point or polynomial oracle. -/
theorem characteristic_root_of_minimizer (ell : ℕ) (hell : 1 ≤ ell)
    (a : Fin n → ℝ) (F : MvPolynomial (Fin n) ℝ) (hF : F.totalDegree ≤ ell)
    (u : ℝ) (x : Fin n → ℝ) (hx : IsMinOn (criticalObjective ell a F u) univ x) :
    ((multiplicationMatrix hell (criticalLower ell a u F)
      (criticalLower_degree ell hell a u F hF) (deformedPolynomial ell a u F)).charpoly).eval
        (criticalObjective ell a F u x) = 0 := by
  have h := charpoly_eval_at_common_zero hell (criticalLower ell a u F)
    (criticalLower_degree ell hell a u F hF) (deformedPolynomial ell a u F) x
    (critical_equations_of_minimizer ell a F u x hx)
  simpa only [MvPolynomial.aeval_eq_eval, Polynomial.coe_aeval_eq_eval,
    ← criticalObjective_eq_eval] using h

end LeanCanny.CountingHierarchy
