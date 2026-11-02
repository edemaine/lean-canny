/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PaddedIntegralNormalization
/-! # Exact removal of zero roots introduced by scalar padding

A root of a padded normalization recovers the original polynomial root
away from zero. At zero, the original constant coefficient is the exact
remaining test. This also rejects padding roots of degree-zero nonzero
polynomials; no division by a potentially nonunit integer is performed.
-/
@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralNormalization
open Polynomial
open scoped Classical
variable {R K : Type*} [CommRing R] [Field K]

theorem scaled_root_converse (p : Polynomial R) (d N : ℕ) (hdN : d≤N) (φ : R→+*K)
    (hd : (p.map φ).natDegree=d) (ha : φ (p.coeff d)≠0) (a : K) (ha0 : a≠0)
    (hz : (polynomial p d N).eval₂ φ (φ (p.coeff d)*a)=0) : p.eval₂ φ a=0 := by
  have hy : φ (p.coeff d)*a≠0 := mul_ne_zero ha ha0
  have HZ : (FixedDegreeIntegralNormalization.polynomial p d).eval₂ φ (φ (p.coeff d)*a)=0 := by
    rw [polynomial,ite_eq_left hdN,eval₂_mul,eval₂_pow,eval₂_X] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hy)
  by_cases hzero : d=0
  · rw [hzero] at HZ
    simp only [FixedDegreeIntegralNormalization.polynomial,pow_zero,Finset.range_zero,Finset.sum_empty,
      add_zero,eval₂_one] at HZ
    exact (one_ne_zero HZ).elim
  · have hp : p.map φ≠0 := by
      intro he
      have HC := congrArg (fun q : Polynomial K=>q.coeff d) he
      simp only [coeff_map,coeff_zero] at HC
      exact ha HC
    have HC : (p.map φ).leadingCoeff=φ (p.coeff d) := by rw [leadingCoeff,hd,coeff_map]
    have HE := integralNormalization_eval₂_leadingCoeff_mul (p:=p.map φ) (by omega) (RingHom.id K) a
    have HV := congrArg (fun q : Polynomial K=>q.eval (φ (p.coeff d)*a))
      (FixedDegreeIntegralNormalization.map_eq_integralNormalization p d φ hp hd)
    simp only [eval_map] at HV
    rw [HV,←HC] at HZ
    have Hmul : (p.map φ).leadingCoeff^(d-1)*p.eval₂ φ a=0 := by
      simpa only [RingHom.id_apply,eval₂_id,hd,eval_map] using HE.symm.trans HZ
    exact (mul_eq_zero.mp Hmul).resolve_left (pow_ne_zero _ (HC.symm ▸ ha))

theorem root_guard (p : Polynomial R) (d N : ℕ) (hdN : d≤N) (φ : R→+*K)
    (hd : (p.map φ).natDegree=d) (ha : φ (p.coeff d)≠0) (a : K)
    (hz : (polynomial p d N).eval₂ φ (φ (p.coeff d)*a)=0) :
    p.eval₂ φ a=0 ↔ a≠0 ∨ φ (p.coeff 0)=0 := by
  constructor
  · intro hp
    by_cases h : a=0
    · right
      simpa only [h,eval₂_at_zero] using hp
    · exact Or.inl h
  · intro hg
    by_cases h : a=0
    · have HC : φ (p.coeff 0)=0 := hg.resolve_left (fun hne=>hne h)
      simpa only [h,eval₂_at_zero] using HC
    · exact scaled_root_converse p d N hdN φ hd ha a h hz

end LeanCanny.Algebra.PaddedIntegralNormalization
