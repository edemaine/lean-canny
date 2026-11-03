/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CommonDenominatorSpecialization
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Mass of exact total-degree common-denominator clearing -/
@[expose] public section
namespace LeanCanny.Algebra.CommonDenominatorSpecialization
open MvPolynomial
open scoped BigOperators Classical
variable {σ τ : Type*} [Fintype σ]

theorem mass (D : ℕ) (q : ℤ) (v : σ→MvPolynomial τ ℤ) (p : MvPolynomial σ ℤ)
    (hp : p.totalDegree≤D) (M : ℕ) (hq : q.natAbs≤M) (hv : ∀ i,MvMass.mass (v i)≤M) :
    MvMass.mass (clear D q v p)≤MvMass.mass p*M^D :=by
  have HF (e : σ→₀ℕ) (he : e.degree≤D) : MvMass.mass (factor D q v e)≤M^D :=by
    unfold factor
    apply (MvMass.mul_le _ _).trans
    rw [MvMass.C,Int.natAbs_pow]
    have HP : MvMass.mass (∏ i,v i^e i)≤M^e.degree :=by
      apply (MvMass.prod_le Finset.univ _).trans
      have H:=Finset.prod_le_prod (fun i (_ : i∈Finset.univ)=>
        (MvMass.pow_le (v i) (e i)).trans (Nat.pow_le_pow_left (hv i) _))
      apply H.trans_eq
      rw [Finset.prod_pow_eq_pow_sum,Finsupp.degree_eq_sum]
    exact (Nat.mul_le_mul (Nat.pow_le_pow_left hq _) HP).trans_eq
      (by rw [←pow_add,Nat.sub_add_cancel he])
  change MvMass.mass (∑ e∈p.support,MvPolynomial.C (p.coeff e)*factor D q v e)≤_
  apply (MvMass.sum_le _ _).trans
  calc
    _≤∑ e∈p.support,(p.coeff e).natAbs*M^D :=by
      apply Finset.sum_le_sum
      intro e he
      exact (MvMass.mul_le _ _).trans
        (by rw [MvMass.C];exact Nat.mul_le_mul_left _ (HF e ((MvPolynomial.le_totalDegree he).trans hp)))
    _=MvMass.mass p*M^D:=by rw [MvMass.mass,Finset.sum_mul]

end LeanCanny.Algebra.CommonDenominatorSpecialization
