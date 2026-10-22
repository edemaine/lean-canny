/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-!
# Sign-preserving rational coordinate substitution

For coordinate ratios `nᵢ/dᵢ`, multiply a multivariate polynomial by the common
denominator `∏ dᵢ^(2*degreeOfᵢ p)`. Every denominator exponent is even. Expanding
monomials gives an explicit univariate numerator, with the same sign wherever
the coordinate denominators are nonzero. This is the denominator-clearing step
of Canny's Lemma 2.4; it includes constant and zero inputs and empty coordinate
families. The degree estimate does not construct the expanded polynomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial
open scoped BigOperators

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

noncomputable def denominator (p : MvPolynomial σ R) (d : σ → R[X]) : R[X] :=
  ∏ i, d i ^ (2 * p.degreeOf i)

noncomputable def clearedWith (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X]) : R[X] :=
  ∑ e ∈ p.support, C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)

noncomputable def cleared (p : MvPolynomial σ R) (n d : σ → R[X]) : R[X] :=
  ∑ e ∈ p.support, C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * p.degreeOf i - e i)

theorem scale_div_pow {K : Type*} [Field K] (a b : K) (s e : ℕ) (he : e ≤ s) (hb : b ≠ 0) :
    b ^ s * (a / b) ^ e = a ^ e * b ^ (s - e) := by
  rw [div_pow, ← mul_div_assoc]
  apply (div_eq_iff (pow_ne_zero _ hb)).mpr
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel he]
  ring

theorem eval₂_clearedWith {K : Type*} [Field K] (φ : R →+* K) (x : K)
    (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X])
    (hD : ∀ i, p.degreeOf i ≤ D i) (hd : ∀ i, (d i).eval₂ φ x ≠ 0) :
    (clearedWith D p n d).eval₂ φ x = (∏ i, (d i).eval₂ φ x ^ (2 * D i)) *
      p.eval₂ φ (fun i => (n i).eval₂ φ x / (d i).eval₂ φ x) := by
  classical
  let ψ := Polynomial.eval₂RingHom φ x
  have hC (a : R) : ψ (C a) = φ a := Polynomial.eval₂_C _ _
  change ψ (clearedWith D p n d) = (∏ i, ψ (d i) ^ (2 * D i)) *
    p.eval₂ φ (fun i => ψ (n i) / ψ (d i))
  simp only [clearedWith, map_sum, map_mul, map_prod, map_pow, hC]
  rw [MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hf (i : σ) : e i ≤ 2 * D i :=
    ((MvPolynomial.monomial_le_degreeOf i he).trans (hD i)).trans (by omega)
  calc
    _ = φ (p.coeff e) * ∏ i, ψ (d i) ^ (2 * D i) * (ψ (n i) / ψ (d i)) ^ e i := by
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (scale_div_pow _ _ _ _ (hf i) (hd i)).symm)
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem eval₂_cleared {K : Type*} [Field K] (φ : R →+* K) (x : K)
    (p : MvPolynomial σ R) (n d : σ → R[X]) (hd : ∀ i, (d i).eval₂ φ x ≠ 0) :
    (cleared p n d).eval₂ φ x = (denominator p d).eval₂ φ x *
      p.eval₂ φ (fun i => (n i).eval₂ φ x / (d i).eval₂ φ x) := by
  classical
  have hden : (denominator p d).eval₂ φ x = ∏ i, (d i).eval₂ φ x ^ (2 * p.degreeOf i) := by
    change (Polynomial.eval₂RingHom φ x) _ = _
    simp only [denominator, map_prod, map_pow, Polynomial.coe_eval₂RingHom]
  rw [hden]
  exact eval₂_clearedWith φ x p.degreeOf p n d (fun _ => le_rfl) hd

theorem denominator_eval₂_pos (φ : R →+* ℝ) (x : ℝ)
    (p : MvPolynomial σ R) (d : σ → R[X]) (hd : ∀ i, (d i).eval₂ φ x ≠ 0) :
    0 < (denominator p d).eval₂ φ x := by
  classical
  change 0 < (Polynomial.eval₂RingHom φ x) (denominator p d)
  simp only [denominator, map_prod, map_pow]
  change 0 < ∏ i, ((d i).eval₂ φ x) ^ (2 * p.degreeOf i)
  apply Finset.prod_pos
  intro i _
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero (hd i)) _

theorem sign_eval₂_cleared (φ : R →+* ℝ) (x : ℝ)
    (p : MvPolynomial σ R) (n d : σ → R[X]) (hd : ∀ i, (d i).eval₂ φ x ≠ 0) :
    SignType.sign ((cleared p n d).eval₂ φ x) =
      SignType.sign (p.eval₂ φ (fun i => (n i).eval₂ φ x / (d i).eval₂ φ x)) := by
  rw [eval₂_cleared φ x p n d hd, sign_mul, sign_pos (denominator_eval₂_pos φ x p d hd), one_mul]

theorem natDegree_clearedWith_le_sum (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X])
    (hD : ∀ i, p.degreeOf i ≤ D i) :
    (clearedWith D p n d).natDegree ≤ ∑ i, 2 * D i * max (n i).natDegree (d i).natDegree := by
  classical
  unfold clearedWith
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  calc
    (C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)).natDegree ≤
        (C (p.coeff e)).natDegree + (∏ i, n i ^ e i * d i ^ (2 * D i - e i)).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (∏ i, n i ^ e i * d i ^ (2 * D i - e i)).natDegree := by simp only [Polynomial.natDegree_C, Nat.zero_add]
    _ ≤ ∑ i, (n i ^ e i * d i ^ (2 * D i - e i)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, 2 * D i * max (n i).natDegree (d i).natDegree := by
      apply Finset.sum_le_sum
      intro i _
      have hmon : e i ≤ 2 * D i := ((MvPolynomial.monomial_le_degreeOf i he).trans (hD i)).trans (by omega)
      calc
        (n i ^ e i * d i ^ (2 * D i - e i)).natDegree ≤
            (n i ^ e i).natDegree + (d i ^ (2 * D i - e i)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ e i * (n i).natDegree + (2 * D i - e i) * (d i).natDegree :=
          Nat.add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le
        _ ≤ e i * max (n i).natDegree (d i).natDegree +
            (2 * D i - e i) * max (n i).natDegree (d i).natDegree :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_left _ _)) (Nat.mul_le_mul_left _ (le_max_right _ _))
        _ = 2 * D i * max (n i).natDegree (d i).natDegree := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hmon]

theorem natDegree_cleared_le (p : MvPolynomial σ R) (n d : σ → R[X]) :
    (cleared p n d).natDegree ≤ ∑ i, 2 * p.degreeOf i * max (n i).natDegree (d i).natDegree := by
  exact natDegree_clearedWith_le_sum p.degreeOf p n d (fun _ => le_rfl)

end LeanCanny.Algebra.RationalSubstitution
