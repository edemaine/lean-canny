/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PaddedIntegralNormalization
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Algebra.IntegralParameterInverseSpecialization
/-! # Uniform parameter-coefficient bounds for actual monic normalization

The bounds apply before evaluating the parameter and cover every advertised
degree, including degrees larger than the padded rank.
-/
@[expose] public section
namespace LeanCanny.Algebra
open Polynomial

theorem fixed_normalization_coefficient_mass (p :(ℤ[X])[X]) (d b :ℕ)
    (hp :∀i,coefficientMass (p.coeff i)≤2^b) (k :ℕ):
    coefficientMass ((FixedDegreeIntegralNormalization.polynomial p d).coeff k)≤2^(b*d):=by
  rw [FixedDegreeIntegralNormalization.coefficient]
  by_cases he :k=d
  · subst k
    simp only [ite_true,Nat.lt_irrefl,ite_false,add_zero]
    simpa only [←Polynomial.C_1,coefficientMass_C,Int.natAbs_one] using
      (show (1:ℕ)≤2^(b*d) from Nat.one_le_two_pow)
  · rw [ite_eq_right he,zero_add]
    by_cases hk :k<d
    · rw [ite_eq_left hk]
      calc
        _≤coefficientMass (p.coeff k)*coefficientMass (p.coeff d)^(d-1-k):=
          (coefficientMass_mul_le _ _).trans (Nat.mul_le_mul_left _ (coefficientMass_pow_le _ _))
        _≤2^b*(2^b)^(d-1-k):=Nat.mul_le_mul (hp k) (Nat.pow_le_pow_left (hp d) _)
        _=2^(b*(1+(d-1-k))):=by rw [←pow_mul,←pow_add];congr 1;ring
        _≤2^(b*d):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b (by omega))
    · rw [ite_eq_right hk]
      simp

theorem padded_normalization_coefficient_mass (p :(ℤ[X])[X]) (d N b :ℕ)
    (hp :∀i,coefficientMass (p.coeff i)≤2^b) (k :ℕ):
    coefficientMass ((PaddedIntegralNormalization.polynomial p d N).coeff k)≤2^(b*N):=by
  rw [PaddedIntegralNormalization.coefficient]
  by_cases hd :d≤N
  · rw [ite_eq_left hd]
    split_ifs
    · exact (fixed_normalization_coefficient_mass p d b hp _).trans
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b hd))
    · simp
  · rw [ite_eq_right hd]
    split_ifs
    · simpa only [←Polynomial.C_1,coefficientMass_C,Int.natAbs_one] using
        (show (1:ℕ)≤2^(b*N) from Nat.one_le_two_pow)
    · simp

theorem fixed_normalization_coefficient_degree (p :(ℤ[X])[X]) (d δ :ℕ)
    (hp :∀i,(p.coeff i).natDegree≤δ) (k :ℕ):
    ((FixedDegreeIntegralNormalization.polynomial p d).coeff k).natDegree≤d*δ:=by
  rw [FixedDegreeIntegralNormalization.coefficient]
  by_cases he :k=d
  · subst k
    simp
  · rw [ite_eq_right he,zero_add]
    by_cases hk :k<d
    · rw [ite_eq_left hk]
      calc
        _≤(p.coeff k).natDegree+(d-1-k)*(p.coeff d).natDegree:=
          natDegree_mul_le.trans (Nat.add_le_add_left natDegree_pow_le _)
        _≤δ+(d-1-k)*δ:=Nat.add_le_add (hp k) (Nat.mul_le_mul_left _ (hp d))
        _=(1+(d-1-k))*δ:=by ring
        _≤d*δ:=Nat.mul_le_mul_right δ (by omega)
    · rw [ite_eq_right hk]
      simp

theorem padded_normalization_coefficient_degree (p :(ℤ[X])[X]) (d N δ :ℕ)
    (hp :∀i,(p.coeff i).natDegree≤δ) (k :ℕ):
    ((PaddedIntegralNormalization.polynomial p d N).coeff k).natDegree≤N*δ:=by
  rw [PaddedIntegralNormalization.coefficient]
  by_cases hd :d≤N
  · rw [ite_eq_left hd]
    split_ifs
    · exact (fixed_normalization_coefficient_degree p d δ hp _).trans
        (Nat.mul_le_mul_right δ hd)
    · simp
  · rw [ite_eq_right hd]
    split_ifs <;> simp

theorem inverseAt_coefficient_mass (p :(ℤ[X])[X]) (τ b :ℕ)
    (hp :∀i,coefficientMass (p.coeff i)≤2^b) (k :ℕ):
    coefficientMass ((IntegralParameterInverse.inverseAt p τ).coeff k)≤2^b:=by
  rw [IntegralParameterInverse.coeff_inverseAt,coefficientMass_neg]
  exact hp _

theorem inverseAt_coefficient_degree (p :(ℤ[X])[X]) (τ δ :ℕ)
    (hp :∀i,(p.coeff i).natDegree≤δ) (k :ℕ):
    ((IntegralParameterInverse.inverseAt p τ).coeff k).natDegree≤δ:=by
  rw [IntegralParameterInverse.coeff_inverseAt,Polynomial.natDegree_neg]
  exact hp _

end LeanCanny.Algebra
