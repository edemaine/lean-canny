/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAlgebraicZeros
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Ideal

/-! # Clearing denominators of generic coordinate annihilators

An annihilator over a fraction field can be cleared to a nonzero polynomial
over the parameter ring. A further nonzero parameter multiple puts its
coordinate evaluation in the original radical ideal. These certificates can
be specialized wherever their parameter factors remain nonzero.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteFiberSpecialization
open MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A F ι : Type*} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]

omit [IsDomain A] [Algebra A F] [IsFractionRing A F] in
theorem map_coordinate_aeval (φ : A →+* F) (i : ι) (q : Polynomial A) :
    (Polynomial.aeval (X i : MvPolynomial ι A) q).map φ =
      Polynomial.aeval (X i : MvPolynomial ι F) (q.map φ) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, map_mul, map_pow,
      MvPolynomial.algebraMap_eq, map_C, map_X]

theorem exists_cleared_annihilator (I : Ideal (MvPolynomial ι A)) (i : ι) (q : Polynomial F)
    (hq : q ≠ 0)
    (hm : Polynomial.aeval (X i : MvPolynomial ι F) q ∈
      (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).radical) :
    ∃ Q : Polynomial A, Q ≠ 0 ∧ ∃ s : A, s ≠ 0 ∧
      C s * Polynomial.aeval (X i : MvPolynomial ι A) Q ∈ I.radical := by
  let Q := IsLocalization.integerNormalization (nonZeroDivisors A) q
  have hQ : Q ≠ 0 := fun h => hq ((IsLocalization.integerNormalization_eq_zero_iff le_rfl q).mp h)
  obtain ⟨b, hb, hQmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) q
  have hmap : algebraMap (MvPolynomial ι A) (MvPolynomial ι F)
      (Polynomial.aeval (X i : MvPolynomial ι A) Q) ∈
        (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).radical := by
    rw [MvPolynomial.algebraMap_def, map_coordinate_aeval]
    change Polynomial.aeval (X i : MvPolynomial ι F)
      ((IsLocalization.integerNormalization (nonZeroDivisors A) q).map (algebraMap A F)) ∈ _
    rw [hQmap, ← IsScalarTower.algebraMap_smul F b q, map_smul]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    exact Ideal.mul_mem_left _ _ hm
  rw [← IsLocalization.map_radical ((nonZeroDivisors A).map (C (σ := ι))) (MvPolynomial ι F) I] at hmap
  obtain ⟨m, hmM, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := ι))) (MvPolynomial ι F) I.radical _).mp hmap
  obtain ⟨s, hs, rfl⟩ := hmM
  exact ⟨Q, hQ, s, nonZeroDivisors.ne_zero hs, hmI⟩

omit [IsDomain A] in
theorem eval_coordinate_aeval {S : Type*} [CommRing S] (φ : A →+* S) (x : ι → S)
    (i : ι) (q : Polynomial A) :
    (Polynomial.aeval (X i : MvPolynomial ι A) q).eval₂ φ x = Polynomial.eval₂ φ (x i) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Polynomial.eval₂_monomial, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

universe uL

theorem finite_specialization_of_certificates [Fintype ι]
    (I : Ideal (MvPolynomial ι A)) (Q : ι → Polynomial A) (s : ι → A)
    (hQ : ∀ i, Q i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (hm : ∀ i, C (s i) * Polynomial.aeval (X i : MvPolynomial ι A) (Q i) ∈ I.radical) :
    ∃ d : A, d ≠ 0 ∧ ∀ (L : Type uL) [Field L] (φ : A →+* L), φ d ≠ 0 →
      {x : ι → L | ∀ p ∈ I, p.eval₂ φ x = 0}.Finite := by
  classical
  let d : A := ∏ i, s i * (Q i).leadingCoeff
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ =>
    mul_ne_zero (hs i) (Polynomial.leadingCoeff_ne_zero.mpr (hQ i)))
  refine ⟨d, hd, ?_⟩
  intro L _ φ hφ
  have hfac (i : ι) : φ (s i) ≠ 0 ∧ φ (Q i).leadingCoeff ≠ 0 := by
    have hp : ∏ i, φ (s i * (Q i).leadingCoeff) ≠ 0 := by simpa only [d, map_prod] using hφ
    have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
    rw [map_mul] at hi
    exact mul_ne_zero_iff.mp hi
  have hmap (i : ι) : (Q i).map φ ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    simpa only [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ (hfac i).2] using (hfac i).2
  apply (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hmap i))).subset
  intro x hx i
  obtain ⟨n, hn⟩ := hm i
  have he := hx _ hn
  rw [MvPolynomial.eval₂_pow] at he
  have hz := eq_zero_of_pow_eq_zero he
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, eval_coordinate_aeval] at hz
  have hroot := (mul_eq_zero.mp hz).resolve_left (hfac i).1
  change Polynomial.eval (x i) ((Q i).map φ) = 0
  rw [Polynomial.eval_map]
  exact hroot

theorem exists_finite_specialization_certificate [Fintype ι] (I : Ideal (MvPolynomial ι A))
    (hcoords : ∀ P ∈ (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).minimalPrimes,
      ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i)) :
    ∃ d : A, d ≠ 0 ∧ ∀ (L : Type uL) [Field L] (φ : A →+* L), φ d ≠ 0 →
      {x : ι → L | ∀ p ∈ I, p.eval₂ φ x = 0}.Finite := by
  choose q hq hm using FiniteAlgebraicZeros.exists_coordinate_annihilator
    (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))) hcoords
  have h (i : ι) := exists_cleared_annihilator I i (q i) (hq i) (hm i)
  choose Q hQ s hs hsI using h
  exact finite_specialization_of_certificates I Q s hQ hs hsI

end LeanCanny.Algebra.FiniteFiberSpecialization
