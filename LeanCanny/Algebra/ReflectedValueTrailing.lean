/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Polynomial.Reverse
/-! # The value certificate's first coefficient is the original leading one

For a nonzero polynomial of degree at most D, multiplying its D-reflection
by X places its leading coefficient at D-degree+1. Thus the Gram degree and
leading-coefficient covariance determine the actual trailing choice.
-/
@[expose] public section
namespace LeanCanny.Algebra.ReflectedValueTrailing
open Polynomial
variable {R : Type*} [Semiring R]

theorem coefficient (p : R[X]) (D : ℕ) (hd : p.natDegree≤D) :
    (X*p.reflect D).coeff (D-p.natDegree+1)=p.leadingCoeff :=by
  rw [Polynomial.coeff_X_mul,Polynomial.coeff_reflect,Polynomial.revAt_le (by omega)]
  have HE : D-(D-p.natDegree)=p.natDegree:=by omega
  rw [HE,Polynomial.coeff_natDegree]

theorem below (p : R[X]) (D : ℕ) (hd : p.natDegree≤D) (k : ℕ)
    (hk : k<D-p.natDegree+1) : (X*p.reflect D).coeff k=0 :=by
  cases k with
  | zero=>simp only [Polynomial.coeff_X_mul_zero]
  | succ k=>
    rw [Polynomial.coeff_X_mul,Polynomial.coeff_reflect,Polynomial.revAt_le (by omega)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem trailing_degree (p : R[X]) (hp : p≠0) (D : ℕ) (hd : p.natDegree≤D) :
    (X*p.reflect D).natTrailingDegree=D-p.natDegree+1 :=by
  have HC : (X*p.reflect D).coeff (D-p.natDegree+1)≠0:=by
    rw [coefficient p D hd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have HN : X*p.reflect D≠0:=fun hz=>HC (by rw [hz,Polynomial.coeff_zero])
  exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero HC)
    (Polynomial.le_natTrailingDegree HN (fun k hk=>below p D hd k hk))

theorem trailing_coefficient (p : R[X]) (hp : p≠0) (D : ℕ) (hd : p.natDegree≤D) :
    (X*p.reflect D).trailingCoeff=p.leadingCoeff :=by
  change (X*p.reflect D).coeff (X*p.reflect D).natTrailingDegree=p.leadingCoeff
  rw [trailing_degree p hp D hd]
  exact coefficient p D hd

end LeanCanny.Algebra.ReflectedValueTrailing
