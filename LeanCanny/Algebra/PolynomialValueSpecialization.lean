/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteFiberSpecialization
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Specialization certificates for polynomial values on finite systems

Algebraicity of every generic solution coordinate implies algebraicity of
every polynomial test value. Minimal-prime annihilators and denominator
clearing give a nonzero parameter-ring polynomial annihilating that value,
up to one nonzero parameter factor. No degree or coefficient bound is claimed.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialValueSpecialization
open MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.algebraMvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

lemma algebraic_value (u : MvPolynomial ι K) (x : ι → L)
    (hx : ∀ i, IsAlgebraic K (x i)) : IsAlgebraic K (aeval x u) := by
  induction u using MvPolynomial.induction_on with
  | C a => simpa only [aeval_C] using isAlgebraic_algebraMap (A := L) a
  | add u v hu hv => simpa only [map_add] using hu.add hv
  | mul_X u i hu => simpa only [map_mul, aeval_X] using hu.mul (hx i)

variable [Fintype ι]

lemma exists_annihilator (I : Ideal (MvPolynomial ι K))
    (hcoords : ∀ P ∈ I.minimalPrimes, ∀ i, IsAlgebraic K (FiniteAlgebraicZeros.quotientPoint P i))
    (u : MvPolynomial ι K) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval u q ∈ I.radical := by
  classical
  let S := I.minimalPrimes
  let : Fintype S := I.finite_minimalPrimes_of_isNoetherianRing.fintype
  have h (P : S) : ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval u q ∈ P.val := by
    let : P.val.IsPrime := P.property.isPrime
    obtain ⟨q, hq, heq⟩ := algebraic_value u (FiniteAlgebraicZeros.quotientPoint P.val)
      (hcoords P.val P.property)
    refine ⟨q, hq, ?_⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (IsFractionRing.injective (MvPolynomial ι K ⧸ P.val) (FractionRing (MvPolynomial ι K ⧸ P.val)))
    rw [map_zero, ← FiniteAlgebraicZeros.eval_quotientPoint, ← Polynomial.aeval_algHom_apply]
    exact heq
  choose q hq hm using h
  refine ⟨∏ P : S, q P, Finset.prod_ne_zero_iff.mpr (fun P _ => hq P), ?_⟩
  rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
  intro P hP
  rw [map_prod]
  exact P.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨P, hP⟩ : S))) (hm ⟨P, hP⟩)

section Clearing
variable {A F : Type*} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]

omit [Fintype ι] [IsDomain A] [Algebra A F] [IsFractionRing A F] in
lemma map_value_aeval (φ : A →+* F) (u : MvPolynomial ι A) (q : Polynomial A) :
    (Polynomial.aeval u q).map φ = Polynomial.aeval (u.map φ) (q.map φ) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, map_mul, map_pow,
      MvPolynomial.algebraMap_eq, map_C]

/-- Clear both the value annihilator and its radical-ideal identity. -/
lemma exists_cleared_annihilator (I : Ideal (MvPolynomial ι A)) (u : MvPolynomial ι A)
    (hcoords : ∀ P ∈ (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).minimalPrimes,
      ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i)) :
    ∃ Q : Polynomial A, Q ≠ 0 ∧ ∃ s : A, s ≠ 0 ∧
      C s * Polynomial.aeval u Q ∈ I.radical := by
  obtain ⟨q, hq, hm⟩ := exists_annihilator
    (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))) hcoords (u.map (algebraMap A F))
  let Q := IsLocalization.integerNormalization (nonZeroDivisors A) q
  have hQ : Q ≠ 0 := fun h => hq ((IsLocalization.integerNormalization_eq_zero_iff le_rfl q).mp h)
  obtain ⟨b, hb, hQmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) q
  have hmap : algebraMap (MvPolynomial ι A) (MvPolynomial ι F) (Polynomial.aeval u Q) ∈
      (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).radical := by
    rw [MvPolynomial.algebraMap_def, map_value_aeval]
    change Polynomial.aeval (u.map (algebraMap A F))
      ((IsLocalization.integerNormalization (nonZeroDivisors A) q).map (algebraMap A F)) ∈ _
    rw [hQmap, ← IsScalarTower.algebraMap_smul F b q, map_smul]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    exact Ideal.mul_mem_left _ _ hm
  rw [← IsLocalization.map_radical ((nonZeroDivisors A).map (C (σ := ι))) (MvPolynomial ι F) I] at hmap
  obtain ⟨m, hmM, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := ι))) (MvPolynomial ι F) I.radical _).mp hmap
  obtain ⟨s, hs, rfl⟩ := hmM
  exact ⟨Q, hQ, s, nonZeroDivisors.ne_zero hs, hmI⟩

/-- The ideal of independent coordinate equations, retaining multiplicities. -/
noncomputable def gridIdeal (p : ι → Polynomial A) : Ideal (MvPolynomial ι A) :=
  Ideal.span (Set.range (fun i => (p i).toMvPolynomial i))

omit [Fintype ι] [IsDomain A] in
lemma grid_coordinates_algebraic (p : ι → Polynomial A) (hp : ∀ i, p i ≠ 0)
    (P : Ideal (MvPolynomial ι F))
    (hP : P ∈ ((gridIdeal p).map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).minimalPrimes) :
    ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i) := by
  let : P.IsPrime := hP.isPrime
  intro i
  refine ⟨(p i).map (algebraMap A F),
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective A F)).mpr (hp i), ?_⟩
  have hm : (Polynomial.aeval (X i : MvPolynomial ι A) (p i)).map (algebraMap A F) ∈ P := by
    simpa only [MvPolynomial.algebraMap_def, Polynomial.toMvPolynomial] using
      hP.le (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i)))
  have hz : MvPolynomial.aeval (FiniteAlgebraicZeros.quotientPoint P)
      ((Polynomial.aeval (X i : MvPolynomial ι A) (p i)).map (algebraMap A F)) = 0 := by
    rw [FiniteAlgebraicZeros.eval_quotientPoint, Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  rw [map_value_aeval, map_X, ← Polynomial.aeval_algHom_apply, aeval_X] at hz
  exact hz

include F in
/-- Polynomial values on every coordinate-grid root admit a nonzero cleared
annihilator, including when some coordinate equations have repeated roots. -/
lemma exists_grid_annihilator (p : ι → Polynomial A) (hp : ∀ i, p i ≠ 0)
    (u : MvPolynomial ι A) :
    ∃ Q : Polynomial A, Q ≠ 0 ∧ ∃ s : A, s ≠ 0 ∧
      C s * Polynomial.aeval u Q ∈ (gridIdeal p).radical :=
  exists_cleared_annihilator (F := F) (gridIdeal p) u (grid_coordinates_algebraic p hp)

include F in
/-- Absorbing the clearing factor gives a relation valid at every parameter,
including the parameters where that factor vanishes. -/
lemma exists_grid_value_annihilator (p : ι → Polynomial A) (hp : ∀ i, p i ≠ 0)
    (u : MvPolynomial ι A) :
    ∃ Q : Polynomial A, Q ≠ 0 ∧ Polynomial.aeval u Q ∈ (gridIdeal p).radical := by
  obtain ⟨Q, hQ, s, hs, hm⟩ := exists_grid_annihilator (F := F) p hp u
  refine ⟨Polynomial.C s * Q, mul_ne_zero (Polynomial.C_ne_zero.mpr hs) hQ, ?_⟩
  simpa only [map_mul, Polynomial.aeval_C, MvPolynomial.algebraMap_eq] using hm

end Clearing

section Evaluation
variable {A : Type*} [CommRing A]

omit [Fintype ι] in
lemma eval_value_aeval (φ : A →+* K) (x : ι → K) (u : MvPolynomial ι A) (q : Polynomial A) :
    (Polynomial.aeval u q).eval₂ φ x = q.eval₂ φ (u.eval₂ φ x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Polynomial.eval₂_monomial, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C]

omit [Fintype ι] in
lemma eval_eq_zero (I : Ideal (MvPolynomial ι A)) (u : MvPolynomial ι A)
    (Q : Polynomial A) (s : A) (hm : C s * Polynomial.aeval u Q ∈ I.radical)
    (φ : A →+* K) (hs : φ s ≠ 0) (x : ι → K) (hx : ∀ p ∈ I, p.eval₂ φ x = 0) :
    Q.eval₂ φ (u.eval₂ φ x) = 0 := by
  obtain ⟨n, hn⟩ := hm
  have he := hx _ hn
  rw [MvPolynomial.eval₂_pow] at he
  have hz := eq_zero_of_pow_eq_zero he
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, eval_value_aeval] at hz
  exact (mul_eq_zero.mp hz).resolve_left hs

omit [Fintype ι] in
lemma eval_annihilator (I : Ideal (MvPolynomial ι A)) (u : MvPolynomial ι A)
    (Q : Polynomial A) (hm : Polynomial.aeval u Q ∈ I.radical)
    (φ : A →+* K) (x : ι → K) (hx : ∀ p ∈ I, p.eval₂ φ x = 0) :
    Q.eval₂ φ (u.eval₂ φ x) = 0 := by
  obtain ⟨n, hn⟩ := hm
  have he := hx _ hn
  rw [MvPolynomial.eval₂_pow, eval_value_aeval] at he
  exact eq_zero_of_pow_eq_zero he

end Evaluation
end LeanCanny.Algebra.PolynomialValueSpecialization
