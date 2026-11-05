/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CriticalValueAnnihilator
public import LeanCanny.Algebra.FiniteFiberSpecialization
public import Mathlib.Basic.Real.Basic
/-! # A parameter family annihilating regularized norm-boundary critical values

The actual Lagrangian is formed over the integer parameter ring. Its generic
gradient-ideal identity is cleared through localization before specialization.
Thus the multiplier may be unbounded; no finite critical-point locus or
regularity premise is required. No quantitative bound or radius stabilization
is asserted.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParameterizedBoundaryCriticalValues
open MvPolynomial
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.algebraMvPolynomial
set_option backward.isDefEq.respectTransparency false

private noncomputable def gradient {A ι : Type*} [CommRing A] (p : MvPolynomial ι A) :
    Ideal (MvPolynomial ι A) := Ideal.span (Set.range fun i => pderiv i p)

private theorem map_aeval {A B ι : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : MvPolynomial ι A) (Q : Polynomial A) :
    (Polynomial.aeval p Q).map φ = Polynomial.aeval (p.map φ) (Q.map φ) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.map_add,map_add,hP,hQ]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial,Polynomial.map_monomial,map_mul,map_pow,
      MvPolynomial.algebraMap_eq,map_C]

private theorem gradient_map {A B ι : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : MvPolynomial ι A) :
    (gradient p).map (MvPolynomial.map φ) = gradient (p.map φ) := by
  simp only [gradient,Ideal.map_span,pderiv_map]
  rw [←Set.range_comp']

private theorem cleared_certificate {A F ι : Type*} [CommRing A] [IsDomain A]
    [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F] [Fintype ι]
    (p : MvPolynomial ι A) :
    ∃ Q : Polynomial A, Q ≠ 0 ∧ ∃ s : A, s ≠ 0 ∧
      C s * Polynomial.aeval p Q ∈ (gradient p).radical := by
  obtain ⟨r,hr,hm⟩ := CriticalValueAnnihilator.exists_annihilator (p.map (algebraMap A F))
  change Polynomial.aeval (p.map (algebraMap A F)) r ∈ (gradient (p.map (algebraMap A F))).radical at hm
  let Q := IsLocalization.integerNormalization (nonZeroDivisors A) r
  have hQ : Q ≠ 0 := fun h => hr ((IsLocalization.integerNormalization_eq_zero_iff le_rfl r).mp h)
  obtain ⟨b,hb,hQmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) r
  have hmap : algebraMap (MvPolynomial ι A) (MvPolynomial ι F) (Polynomial.aeval p Q) ∈
      ((gradient p).map
        (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).radical := by
    rw [MvPolynomial.algebraMap_def,map_aeval,gradient_map]
    change Polynomial.aeval (p.map (algebraMap A F))
      ((IsLocalization.integerNormalization (nonZeroDivisors A) r).map (algebraMap A F)) ∈ _
    rw [hQmap,←IsScalarTower.algebraMap_smul F b r,map_smul]
    rw [Algebra.smul_def,MvPolynomial.algebraMap_eq]
    exact Ideal.mul_mem_left _ _ hm
  rw [←IsLocalization.map_radical ((nonZeroDivisors A).map (C (σ := ι)))
    (MvPolynomial ι F) (gradient p)] at hmap
  obtain ⟨m,hmM,hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := ι))) (MvPolynomial ι F)
      (gradient p).radical _).mp hmap
  obtain ⟨s,hs,rfl⟩ := hmM
  exact ⟨Q,hQ,s,nonZeroDivisors.ne_zero hs,hmI⟩

private theorem eval_aeval {A B ι : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : MvPolynomial ι A) (Q : Polynomial A) (x : ι → B) :
    (Polynomial.aeval p Q).eval₂ φ x = Q.eval₂ φ (p.eval₂ φ x) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,MvPolynomial.eval₂_add,Polynomial.eval₂_add,hP,hQ]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial,Polynomial.eval₂_monomial,MvPolynomial.algebraMap_eq,
      MvPolynomial.eval₂_mul,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_C]

private theorem eval_certificate {A B ι : Type*} [CommRing A] [Field B]
    (φ : A →+* B) (p : MvPolynomial ι A) (Q : Polynomial A) (s : A)
    (hm : C s * Polynomial.aeval p Q ∈ (gradient p).radical)
    (hs : φ s ≠ 0) (x : ι → B) (hx : ∀ i, (pderiv i p).eval₂ φ x = 0) :
    Q.eval₂ φ (p.eval₂ φ x) = 0 := by
  have HI : gradient p ≤ RingHom.ker (MvPolynomial.eval₂Hom φ x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hx i
  obtain ⟨N,hN⟩ := hm
  have H := HI hN
  change ((C s * Polynomial.aeval p Q)^N).eval₂ φ x = 0 at H
  rw [MvPolynomial.eval₂_pow] at H
  have H0 := eq_zero_of_pow_eq_zero H
  rw [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,eval_aeval] at H0
  exact (mul_eq_zero.mp H0).resolve_left hs

variable {n : ℕ}

noncomputable def spatial (q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Option (Fin n)) (Polynomial ℤ) :=
  (MvPolynomial.rename some q).map Polynomial.C

noncomputable def lagrangian (q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Option (Fin n)) (Polynomial ℤ) :=
  (∑ i : Fin n, X (some i)^2) + X none * (spatial q^2 - C Polynomial.X)

theorem spatial_none (q : MvPolynomial (Fin n) ℤ) : pderiv none (spatial q) = 0 := by
  rw [spatial,pderiv_map]
  have H : pderiv none (MvPolynomial.rename some q) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro h
    obtain ⟨i,_hi,he⟩ := mem_vars_rename some q h
    cases he
  rw [H,map_zero]

theorem spatial_some (q : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    pderiv (some i) (spatial q) = spatial (pderiv i q) := by
  rw [spatial,pderiv_map,pderiv_rename (Option.some_injective (Fin n))]
  rfl

theorem lagrangian_none (q : MvPolynomial (Fin n) ℤ) :
    pderiv none (lagrangian q) = spatial q^2 - C Polynomial.X := by
  simp [lagrangian,spatial_none]

theorem lagrangian_some (q : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    pderiv (some i) (lagrangian q) =
      2 * X (some i) + X none * (2 * spatial q * spatial (pderiv i q)) := by
  simp [lagrangian,spatial_some,Pi.single_apply,mul_assoc]

noncomputable def parameter (e : ℝ) : Polynomial ℤ →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) e

theorem parameter_X (e : ℝ) : parameter e Polynomial.X = e :=
  Polynomial.eval₂_X (Int.castRingHom ℝ) e

theorem parameter_comp_C (e : ℝ) : (parameter e).comp Polynomial.C = Int.castRingHom ℝ :=
  Polynomial.eval₂RingHom_comp_C (Int.castRingHom ℝ) e

theorem spatial_eval (q : MvPolynomial (Fin n) ℤ) (e : ℝ) (x : Fin n → ℝ) (lambda : ℝ) :
    (spatial q).eval₂ (parameter e) (fun j => j.elim lambda x) = q.eval₂ (Int.castRingHom ℝ) x := by
  rw [spatial,eval₂_map,eval₂_rename]
  rw [parameter_comp_C]
  rfl

theorem lagrangian_eval (q : MvPolynomial (Fin n) ℤ) (e : ℝ) (x : Fin n → ℝ) (lambda : ℝ) :
    (lagrangian q).eval₂ (parameter e) (fun j => j.elim lambda x) =
      (∑ i, x i^2) + lambda * ((q.eval₂ (Int.castRingHom ℝ) x)^2 - e) := by
  simp only [lagrangian,eval₂_add,eval₂_sum,eval₂_pow,eval₂_X,Option.elim_some,eval₂_mul,
    eval₂_sub,spatial_eval,eval₂_C,Option.elim_none]
  rw [parameter_X]

theorem lagrangian_critical (q : MvPolynomial (Fin n) ℤ) (e : ℝ) (x : Fin n → ℝ) (lambda : ℝ)
    (he : (q.eval₂ (Int.castRingHom ℝ) x)^2 = e)
    (hx : ∀ i, 2 * x i + lambda * (2 * q.eval₂ (Int.castRingHom ℝ) x *
      (pderiv i q).eval₂ (Int.castRingHom ℝ) x) = 0) :
    ∀ j, (pderiv j (lagrangian q)).eval₂ (parameter e) (fun k => k.elim lambda x) = 0 := by
  intro j
  cases j with
  | none =>
    rw [lagrangian_none,eval₂_sub,eval₂_pow,spatial_eval,eval₂_C,he]
    rw [parameter_X,sub_self]
  | some i =>
    simpa only [lagrangian_some,eval₂_add,eval₂_mul,eval₂_ofNat,eval₂_X,
      Option.elim_some,Option.elim_none,spatial_eval] using hx i

theorem exists_family (q : MvPolynomial (Fin n) ℤ) :
    ∃ Q : Polynomial (Polynomial ℤ), Q ≠ 0 ∧ ∃ d : Polynomial ℤ, d ≠ 0 ∧
      ∀ e : ℝ, (parameter e) d ≠ 0 → Q.map (parameter e) ≠ 0 ∧
        ∀ (x : Fin n → ℝ) (lambda : ℝ), (q.eval₂ (Int.castRingHom ℝ) x)^2 = e →
          (∀ i, 2 * x i + lambda * (2 * q.eval₂ (Int.castRingHom ℝ) x *
            (pderiv i q).eval₂ (Int.castRingHom ℝ) x) = 0) →
          Q.eval₂ (parameter e) (∑ i, x i^2) = 0 := by
  obtain ⟨Q,hQ,s,hs,hm⟩ := cleared_certificate (F := FractionRing (Polynomial ℤ)) (lagrangian q)
  refine ⟨Q,hQ,s * Q.leadingCoeff,mul_ne_zero hs (Polynomial.leadingCoeff_ne_zero.mpr hQ),?_⟩
  intro e hd
  have HS : (parameter e) s ≠ 0 := fun h => hd (by rw [map_mul,h,zero_mul])
  have HQ : (parameter e) Q.leadingCoeff ≠ 0 := fun h => hd (by rw [map_mul,h,mul_zero])
  refine ⟨?_,?_⟩
  · apply Polynomial.leadingCoeff_ne_zero.mp
    simpa only [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (parameter e) HQ] using HQ
  · intro x lambda he hx
    have H := eval_certificate (parameter e) (lagrangian q) Q s hm HS
      (fun j => j.elim lambda x) (lagrangian_critical q e x lambda he hx)
    rwa [lagrangian_eval,he,sub_self,mul_zero,add_zero] at H

end LeanCanny.Algebra.ParameterizedBoundaryCriticalValues
