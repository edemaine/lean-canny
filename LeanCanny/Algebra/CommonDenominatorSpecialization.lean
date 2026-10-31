/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitution
public import LeanCanny.Algebra.HomogenizationAdditive

/-! # Multivariate substitution with one common denominator

Homogeneous denominator clearing uses the original total-degree allowance.
Numerators of spatial degree at most one preserve the original spatial
degree. Frozen-coordinate numerators are coefficient constants.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonDenominatorSpecialization
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {σ τ R : Type*} [Fintype σ] [CommRing R]

noncomputable def factor (D : ℕ) (q : R) (v : σ → MvPolynomial τ R) (e : σ →₀ ℕ) : MvPolynomial τ R :=
  C (q ^ (D - e.degree)) * ∏ i, v i ^ e i

noncomputable def clear (D : ℕ) (q : R) (v : σ → MvPolynomial τ R) :
    MvPolynomial σ R →+ MvPolynomial τ R where
  toFun p := Finsupp.sum (AddMonoidAlgebra.coeff p) (fun e a => C a * factor D q v e)
  map_zero' := by simp
  map_add' := by
    intro p t
    change Finsupp.sum (AddMonoidAlgebra.coeff (p + t)) (fun e a => C a * factor D q v e) =
      Finsupp.sum (AddMonoidAlgebra.coeff p) (fun e a => C a * factor D q v e) +
      Finsupp.sum (AddMonoidAlgebra.coeff t) (fun e a => C a * factor D q v e)
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index (fun _ _ => by simp) (fun _ _ _ _ => by simp only [map_add, add_mul])

theorem monomial (D : ℕ) (q : R) (v : σ → MvPolynomial τ R) (e : σ →₀ ℕ) (a : R) :
    clear D q v (MvPolynomial.monomial e a) = C a * factor D q v e := by
  change Finsupp.sum (Finsupp.single e a) (fun e a => C a * factor D q v e) = _
  exact Finsupp.sum_single_index (by simp)

theorem C_mul (D : ℕ) (q a : R) (v : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    clear D q v (C a * p) = C a * clear D q v p := by
  conv_lhs => rw [p.as_sum, Finset.mul_sum]
  rw [map_sum]
  simp only [C_mul_monomial, monomial, map_mul]
  change (∑ e ∈ p.support, C a * C (p.coeff e) * factor D q v e) = _
  rw [show clear D q v p = ∑ e ∈ p.support, C (p.coeff e) * factor D q v e from rfl,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact mul_assoc _ _ _

theorem X_pow (D k : ℕ) (q : R) (v : σ → MvPolynomial τ R) (i : σ) :
    clear D q v (X i ^ k) = C (q ^ (D - k)) * v i ^ k := by
  rw [X_pow_eq_monomial, monomial, map_one, one_mul, factor, Finsupp.degree_single]
  congr 1
  simp [Finsupp.single_apply]

theorem degree (D : ℕ) (q : R) (v : σ → MvPolynomial τ R) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (p : MvPolynomial σ R) : (clear D q v p).totalDegree ≤ p.totalDegree := by
  change (∑ e ∈ p.support, C (p.coeff e) * factor D q v e).totalDegree ≤ _
  apply totalDegree_finsetSum_le
  intro e he
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, Nat.zero_add, factor]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, Nat.zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans _ (le_totalDegree he)
  change (∑ i, (v i ^ e i).totalDegree) ≤ e.degree
  rw [Finsupp.degree_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e i) (hv i))

theorem eval {K : Type*} [Field K] (φ : R →+* K) (D : ℕ) (q : R)
    (v : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (hp : p.totalDegree ≤ D)
    (hq : φ q ≠ 0) (x : τ → K) :
    (clear D q v p).eval₂ φ x = φ q ^ D * p.eval₂ φ (fun i => (v i).eval₂ φ x / φ q) := by
  have HS (e : σ →₀ ℕ) (he : e.degree ≤ D) :
      φ q ^ (D - e.degree) * ∏ i, (v i).eval₂ φ x ^ e i =
        φ q ^ D * ∏ i, ((v i).eval₂ φ x / φ q) ^ e i := by
    simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]
    rw [← mul_div_assoc]
    apply (eq_div_iff (pow_ne_zero _ hq)).mpr
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel he]
  change (∑ e ∈ p.support, C (p.coeff e) * factor D q v e).eval₂ φ x = _
  rw [eval₂_sum, eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have HD : e.degree ≤ D := (MvPolynomial.le_totalDegree he).trans hp
  simp only [eval₂_mul, eval₂_C, factor, eval₂_prod, eval₂_pow, map_pow]
  rw [HS e HD]
  ring

end LeanCanny.Algebra.CommonDenominatorSpecialization
