/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ZeroCenterEvaluation

/-! # Correctness of zero-center objective, relations and Jacobian access -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue
open scoped BigOperators Classical

theorem zeroPotentialResidue_cast {p n : ℕ} [Fact p.Prime] (ell : ℕ) (hell : 1 ≤ ell) (z : List ℕ) :
    (zeroPotentialResidue p n ell z : ZMod p) =
      eval (fun i : Fin n => (z[i.val]?.getD 0 : ZMod p)) (potentialPolynomial ell (fun _ => 0)) := by
  rw [zeroPotentialResidue, max_eq_right (Fact.out : p.Prime).one_le, unaryModularSum_cast,
    potentialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    zero_pow (by omega : ell ≠ 0), zero_pow (Nat.succ_ne_zero ell), mul_zero, map_zero,
    zero_mul, sub_zero, add_zero, map_pow, eval_X]

theorem zeroLowerValue_cast {p n : ℕ} [Fact p.Prime] (F : MvPolynomial (Fin n) (ZMod p))
    (ell u : ℕ) (hell : 1 ≤ ell) (i : Fin n) (z : List ℕ) (value : List ℕ → ℕ)
    (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval (fun j : Fin n => (y[j.val]?.getD 0 : ZMod p)) F) :
    (zeroLowerValue p n u i.val z value : ZMod p) =
      eval (fun j : Fin n => (z[j.val]?.getD 0 : ZMod p))
        (criticalLower ell (fun _ => 0) (u : ZMod p) F i) := by
  rw [zeroLowerValue, modularSub_cast (Fact.out : p.Prime).pos, Nat.cast_zero, Nat.cast_mul,
    firstPartialResidue_cast F i z value hF hp hv]
  simp only [criticalLower, zero_pow (by omega : ell ≠ 0), map_zero, map_sub, map_mul, eval_C]

theorem zeroObjectiveValue_cast {p n : ℕ} [Fact p.Prime] (F : MvPolynomial (Fin n) (ZMod p))
    (ell u : ℕ) (hell : 1 ≤ ell) (z : List ℕ) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval (fun j : Fin n => (y[j.val]?.getD 0 : ZMod p)) F) :
    (zeroObjectiveValue p n ell u z value : ZMod p) =
      eval (fun j : Fin n => (z[j.val]?.getD 0 : ZMod p)) (deformedPolynomial ell (fun _ => 0) (u : ZMod p) F) := by
  rw [zeroObjectiveValue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
    zeroPotentialResidue_cast ell hell, hv, deformedPolynomial, map_add, map_mul, eval_C]

theorem criticalJacobian_center_independent {R : Type*} [CommRing R] {n : ℕ} (ell : ℕ)
    (a b : Fin n → R) (u : R) (F : MvPolynomial (Fin n) R) :
    jacobian ell (criticalLower ell a u F) = jacobian ell (criticalLower ell b u F) := by
  unfold jacobian
  congr 1
  funext i j
  simp only [criticalLower, map_sub, pderiv_C, pderiv_C_mul]

theorem zeroJacobianValue_cast {p n : ℕ} [Fact p.Prime] (F : MvPolynomial (Fin n) (ZMod p))
    (ell u : ℕ) (z : List ℕ) (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval (fun j : Fin n => (y[j.val]?.getD 0 : ZMod p)) F) :
    (criticalJacobianValue p n ell u z value : ZMod p) =
      eval (fun j : Fin n => (z[j.val]?.getD 0 : ZMod p)) (jacobian ell (criticalLower ell (fun _ => 0) (u : ZMod p) F)) := by
  have h := criticalJacobianValue_cast F ell u z value hF hp hv
  rw [criticalJacobian_center_independent ell _ (fun _ => 0)] at h
  exact h

end LeanCanny.CountingHierarchy
