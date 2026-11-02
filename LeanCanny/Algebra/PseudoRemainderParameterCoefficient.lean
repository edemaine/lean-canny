/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PseudoRemainderLinearQuery
public import LeanCanny.Algebra.PolynomialKronecker
/-! # A coefficient in an independent parameter commutes with fixed reduction

The head is independent of this parameter. Query coefficients may still
contain an arbitrary second parameter through the underlying ring.
-/
@[expose] public section
namespace LeanCanny.Algebra.PseudoRemainderParameterCoefficient
open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def coefficient (p : (R[X])[X]) (k : ℕ) : R[X] :=(Polynomial.Bivariate.swap p).coeff k

theorem coefficient_coefficient (p : (R[X])[X]) (k i : ℕ) :
    (coefficient p k).coeff i=(p.coeff i).coeff k :=PolynomialKronecker.swap_coefficient p k i

theorem coefficient_sub (p q : (R[X])[X]) (k : ℕ) :
    coefficient (p-q) k=coefficient p k-coefficient q k :=by
  simp only [coefficient,map_sub,Polynomial.coeff_sub]

theorem coefficient_mul_left (p : R[X]) (g : (R[X])[X]) (k : ℕ) :
    coefficient (p.map Polynomial.C*g) k=p*coefficient g k :=by
  rw [coefficient,map_mul,Polynomial.Bivariate.swap_map_C,Polynomial.coeff_C_mul]
  rfl

theorem coefficient_high (g : (R[X])[X]) (d k : ℕ) :
    coefficient (PseudoRemainder.high d g) k=PseudoRemainder.high d (coefficient g k) :=by
  ext i
  rw [coefficient_coefficient,PseudoRemainder.high_coeff,PseudoRemainder.high_coeff,coefficient_coefficient]

theorem coefficient_step (p : R[X]) (d : ℕ) (hp : p.natDegree≤d) (g : (R[X])[X]) (k : ℕ) :
    coefficient (PseudoRemainder.step (p.map Polynomial.C) d g) k=
      PseudoRemainder.step p d (coefficient g k) :=by
  rw [PseudoRemainder.step_identity (p.map Polynomial.C) d (Polynomial.natDegree_map_le.trans hp),
    PseudoRemainder.step_identity p d hp,Polynomial.coeff_map]
  rw [←Polynomial.map_C]
  rw [coefficient_sub,coefficient_mul_left,coefficient_mul_left,coefficient_high]

theorem coefficient_iterate (p : R[X]) (d N : ℕ) (hp : p.natDegree≤d) (g : (R[X])[X]) (k : ℕ) :
    coefficient ((PseudoRemainder.step (p.map Polynomial.C) d)^[N] g) k=
      (PseudoRemainder.step p d)^[N] (coefficient g k) :=by
  induction N with
  | zero=>rfl
  | succ N ih=>rw [Function.iterate_succ_apply',coefficient_step p d hp,ih,Function.iterate_succ_apply']

theorem coefficient_seed (p : R[X]) (f : (R[X])[X]) (d D : ℕ) (hp : p.natDegree≤d) (k : ℕ) :
    coefficient (PseudoRemainder.seed (p.map Polynomial.C) f d D) k=
      PseudoRemainder.seed p (coefficient f k) d D :=by
  rw [PseudoRemainder.seed,coefficient_iterate p d (2*(D+1)) hp]
  rw [Polynomial.derivative_map,mul_comm f _,coefficient_mul_left]
  rw [mul_comm p.derivative (coefficient f k)]
  rfl

theorem degree_le (g : (R[X])[X]) (k : ℕ) : (coefficient g k).natDegree≤g.natDegree :=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coefficient_coefficient,Polynomial.coeff_eq_zero_of_natDegree_lt hi,Polynomial.coeff_zero]

end LeanCanny.Algebra.PseudoRemainderParameterCoefficient
