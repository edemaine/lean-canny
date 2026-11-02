/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PseudoRemainderMatrix
/-! # The fixed integral Tarski seed is linear in its query

The reduction has a fixed even iteration count. Inputs below the reduction
degree are multiplied by the corresponding power of the declared head
coefficient, including over rings with zero divisors.
-/
@[expose] public section
namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial
variable {R : Type*} [CommRing R]

theorem iterate_add (p f g : R[X]) (d k : ℕ) :
    (step p d)^[k] (f+g)=(step p d)^[k] f+(step p d)^[k] g := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply',ih,step_add,Function.iterate_succ_apply',Function.iterate_succ_apply']

theorem iterate_C_mul (p g : R[X]) (d k : ℕ) (a : R) :
    (step p d)^[k] (C a*g)=C a*(step p d)^[k] g := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply',ih,step_C_mul,Function.iterate_succ_apply']

theorem seed_add (p f g : R[X]) (d D : ℕ) :
    seed p (f+g) d D=seed p f d D+seed p g d D := by
  rw [seed,add_mul,iterate_add]
  rfl

theorem seed_C_mul (p f : R[X]) (d D : ℕ) (a : R) :
    seed p (C a*f) d D=C a*seed p f d D := by
  rw [seed,mul_assoc,iterate_C_mul]
  rfl

theorem low_of_natDegree_lt (g : R[X]) (d : ℕ) (hg : g.natDegree<d) : low d g=g := by
  ext i
  rw [low_coeff]
  split_ifs with hi
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hg.trans_le (Nat.le_of_not_gt hi))).symm

theorem high_of_natDegree_lt (g : R[X]) (d : ℕ) (hg : g.natDegree<d) : high d g=0 := by
  ext i
  rw [high_coeff,Polynomial.coeff_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hg.trans_le (Nat.le_add_left d i))

theorem iterate_below_degree (p g : R[X]) (d k : ℕ) (hg : g.natDegree<d) :
    (step p d)^[k] g=C (p.coeff d^k)*g := by
  have HS : step p d g=C (p.coeff d)*g :=by
    rw [step,low_of_natDegree_lt g d hg,high_of_natDegree_lt g d hg,mul_zero,sub_zero]
  induction k with
  | zero=>simp
  | succ k ih=>
    rw [Function.iterate_succ_apply,HS,iterate_C_mul,ih,←mul_assoc,←map_mul,←pow_succ']

theorem seed_one (p : R[X]) (d D : ℕ) (hd : 0<d) (hp : p.natDegree≤d) :
    seed p 1 d D=C (p.coeff d^(2*(D+1)))*p.derivative := by
  have HG : p.derivative.natDegree<d :=
    (Polynomial.natDegree_derivative_le p).trans_lt (by omega)
  simpa only [seed,one_mul] using iterate_below_degree p p.derivative d (2*(D+1)) HG

theorem seed_constant (p : R[X]) (d D : ℕ) (hd : 0<d) (hp : p.natDegree≤d) (a : R) :
    seed p (C a) d D=C (a*p.coeff d^(2*(D+1)))*p.derivative := by
  have H : C a=C a*(1:R[X]) :=by rw [mul_one]
  rw [H,seed_C_mul,seed_one p d D hd hp,←mul_assoc,←map_mul]

end LeanCanny.Algebra.PseudoRemainder
