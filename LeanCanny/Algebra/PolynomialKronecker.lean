/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientBounds
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Retaining two independent variables in a univariate coefficient computation

The inner variable stays `X` and the outer variable becomes `X^B`. If every
inner coefficient polynomial has degree below `B`, the coefficient at `i+B*j`
recovers exactly the original coefficient at inner degree `i`, outer degree `j`.
The encoding commutes with determinants. A columnwise inner-degree estimate
supplies a sufficient radix for the determinant, rather than just its entries.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialKronecker
open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def encode (B : ℕ) : Polynomial (Polynomial R) →+* Polynomial R :=
  Polynomial.eval₂RingHom (RingHom.id _) (Polynomial.X ^ B)

@[simp] theorem encode_C (B : ℕ) (p : Polynomial R) : encode B (Polynomial.C p) = p := by
  simp [encode, Polynomial.coe_eval₂RingHom]

@[simp] theorem encode_X (B : ℕ) : encode B (Polynomial.X : Polynomial (Polynomial R)) = Polynomial.X ^ B := by
  simp [encode, Polynomial.coe_eval₂RingHom]

theorem encode_monomial (B j : ℕ) (p : Polynomial R) :
    encode B (Polynomial.monomial j p) = p * Polynomial.X ^ (B * j) := by
  simp [encode, Polynomial.coe_eval₂RingHom, pow_mul]

theorem encode_sum (B : ℕ) (p : Polynomial (Polynomial R)) :
    encode B p = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * Polynomial.X ^ (B * j) := by
  conv_lhs => rw [p.as_sum_range]
  simp only [map_sum, encode_monomial]

theorem coefficient (B : ℕ) (p : Polynomial (Polynomial R))
    (hp : ∀ j, (p.coeff j).natDegree < B) (i j : ℕ) (hi : i < B) :
    (encode B p).coeff (i + B * j) = (p.coeff j).coeff i := by
  classical
  rw [encode_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · exact Polynomial.coeff_mul_X_pow (p.coeff j) (B * j) i
  · intro k _ hkj
    rcases Nat.lt_or_gt_of_ne hkj with hk | hk
    · have hb : B * k + B ≤ B * j := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left B (Nat.succ_le_of_lt hk)
      rw [Polynomial.coeff_mul_X_pow', ite_eq_left (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hp k).trans_le (by omega))
    · have hb : B * j + B ≤ B * k := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left B (Nat.succ_le_of_lt hk)
      rw [Polynomial.coeff_mul_X_pow', ite_eq_right (by omega)]
  · intro hj
    have hd : p.natDegree < j := by
      simp only [Finset.mem_range] at hj
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd]
    simp

theorem encode_eq_zero_iff (B : ℕ) (p : Polynomial (Polynomial R))
    (hp : ∀ j, (p.coeff j).natDegree < B) : encode B p = 0 ↔ p = 0 := by
  constructor
  · intro hz
    ext j i
    by_cases hi : i < B
    · have hc := coefficient B p hp i j hi
      rw [hz, Polynomial.coeff_zero] at hc
      simpa only [Polynomial.coeff_zero] using hc.symm
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hp j).trans_le (by omega))]
      simp
  · intro hz
    rw [hz, map_zero]

theorem coefficient_any (B : ℕ) (hB : 0 < B) (p : Polynomial (Polynomial R))
    (hp : ∀ j, (p.coeff j).natDegree < B) (n : ℕ) :
    (encode B p).coeff n = (p.coeff (n / B)).coeff (n % B) := by
  have h := coefficient B p hp (n % B) (n / B) (Nat.mod_lt n hB)
  rw [Nat.mod_add_div] at h
  exact h

theorem swap_coefficient (p : Polynomial (Polynomial R)) (i j : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial k p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial l a =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      simp only [Polynomial.coeff_monomial]
      split_ifs <;> simp_all [Polynomial.coeff_monomial]

theorem inner_degree_iff_swap (p : Polynomial (Polynomial R)) (D : ℕ) :
    (∀ j, (p.coeff j).natDegree ≤ D) ↔ (Polynomial.Bivariate.swap p).natDegree ≤ D := by
  constructor
  · intro hp
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext j
    rw [swap_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt ((hp j).trans_lt hi), Polynomial.coeff_zero]
  · intro hp j
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [← swap_coefficient p i j, Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt hi), Polynomial.coeff_zero]

theorem determinant_inner_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Polynomial R))) (D : ι → ℕ)
    (hD : ∀ r s j, ((A r s).coeff j).natDegree ≤ D s) (j : ℕ) :
    (A.det.coeff j).natDegree ≤ ∑ s, D s := by
  have hd : (Polynomial.Bivariate.swap A.det).natDegree ≤ ∑ s, D s := by
    let φ : Polynomial (Polynomial R) →+* Polynomial (Polynomial R) := Polynomial.Bivariate.swap.toRingHom
    have hm : Polynomial.Bivariate.swap A.det = (A.map φ).det := φ.map_det A
    rw [hm]
    apply det_natDegree_le _ D
    intro r s
    exact (inner_degree_iff_swap (A r s) (D s)).mp (hD r s)
  exact (inner_degree_iff_swap A.det _).mpr hd j

theorem determinant_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Polynomial R))) (D : ι → ℕ)
    (hD : ∀ r s j, ((A r s).coeff j).natDegree ≤ D s) (B : ℕ) (hB : (∑ s, D s) < B)
    (i j : ℕ) (hi : i < B) :
    ((A.map (encode B)).det).coeff (i + B * j) = (A.det.coeff j).coeff i := by
  have hm : encode B A.det = (A.map (encode B)).det := (encode B).map_det A
  rw [← hm]
  exact coefficient B A.det (fun k => (determinant_inner_degree A D hD k).trans_lt hB) i j hi

end LeanCanny.Algebra.PolynomialKronecker
