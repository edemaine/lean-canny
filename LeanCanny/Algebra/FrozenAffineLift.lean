/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FrozenAffineCopies
public import LeanCanny.Algebra.AffineConstantParameterShift
public import Mathlib.Tactic.FinCases

/-! # Lifting a branch and two endpoint candidates to the frozen system

The same extended system captures every pair of endpoint roots at every
retained height root. Its midpoint annihilators therefore work uniformly for
all endpoint candidates, without adding their algebraic coordinates as data.
-/

@[expose] public section
namespace LeanCanny.Algebra.FrozenAffineCopies
open MvPolynomial
open scoped Classical
set_option maxHeartbeats 300000
variable {n : ℕ}

theorem lift {K : Type*} [CommRing K] (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (height : Fin n) (rho : Polynomial ℤ →+* K) (a : K) (current left right : Fin n → K)
    (hE : E.eval₂ (Int.castRingHom K) a = 0)
    (hc : ∀ i, (p i).eval₂ (Int.castRingHom K) current = if i = height then rho Polynomial.X else 0)
    (hl : ∀ i, (p i).eval₂ (Int.castRingHom K) left = if i = height then a else 0)
    (hr : ∀ i, (p i).eval₂ (Int.castRingHom K) right = if i = height then a else 0) :
    ∀ j, (AffineConstantParameterShift.system (system p E height (fun k : Fin 3 => decide (k.val ≠ 0)))
      (fun j => if j = block (0 : Fin 3) height then Polynomial.X else 0) j).eval₂ rho (point a ![current, left, right]) = 0 := by
  apply (AffineConstantParameterShift.roots_iff _ _ rho _).mpr
  have hblock (k : Fin 3) (i : Fin n) :
      (system p E height (fun k : Fin 3 => decide (k.val ≠ 0)) (block k i)).eval₂
        (Int.castRingHom K) (point a ![current, left, right]) =
        rho (if block k i = block (0 : Fin 3) height then Polynomial.X else 0) := by
    rw [system_block, row_eval]
    have he : point a ![current, left, right] ∘ block k = ![current, left, right] k := by
      funext j
      exact point_block a ![current, left, right] k j
    rw [he, point_zero]
    fin_cases k <;> by_cases hi : i = height <;>
      simp [block_eq_iff, hi, hc, hl, hr]
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · have hn : (0 : Fin (3 * n + 1)) ≠ block (0 : Fin 3) height := by
      intro he
      have H := congrArg Fin.val he
      change 0 = (finProdFinEquiv ((0 : Fin 3), height)).val + 1 at H
      omega
    rw [system_zero, IndexedMultivariateRational.eval_parameter, point_zero, ite_eq_right hn, map_zero]
    exact hE
  · have H := hblock (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
    have he : block (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 = j.succ := by
      change (finProdFinEquiv (finProdFinEquiv.symm j)).succ = j.succ
      rw [Equiv.apply_symm_apply]
    rwa [he] at H

end LeanCanny.Algebra.FrozenAffineCopies
