/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CriticalValueAlgebraic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-! # Annihilating polynomials for critical values

Each prime containing the gradient ideal gives an algebraic critical value in
the fraction field of its quotient. Multiplying annihilators for the finitely
many minimal primes yields a nonzero polynomial vanishing on all critical
values. This construction gives no effective degree or coefficient bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.CriticalValueAnnihilator
open MvPolynomial
open scoped BigOperators

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]

theorem exists_mem_prime (p : MvPolynomial ι K) (P : Ideal (MvPolynomial ι K)) [P.IsPrime]
    (hg : ∀ i, pderiv i p ∈ P) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval p q ∈ P := by
  let F := FractionRing (MvPolynomial ι K ⧸ P)
  let φ : MvPolynomial ι K →ₐ[K] F :=
    (IsScalarTower.toAlgHom K (MvPolynomial ι K ⧸ P) F).comp (Ideal.Quotient.mkₐ K P)
  let v : ι → F := fun i => φ (X i)
  have hφ : MvPolynomial.aeval v = φ := by ext i; simp [v]
  have hv : ∀ i, MvPolynomial.aeval v (pderiv i p) = 0 := by
    intro i
    rw [hφ]
    change algebraMap (MvPolynomial ι K ⧸ P) F (Ideal.Quotient.mk P (pderiv i p)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hg i), map_zero]
  obtain ⟨q, hq, hqv⟩ := CriticalValueAlgebraic.algebraic_of_gradient_zero p v hv
  refine ⟨q, hq, ?_⟩
  rw [hφ] at hqv
  have he : φ (Polynomial.aeval p q) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]
    exact hqv
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (IsFractionRing.injective (MvPolynomial ι K ⧸ P) F)
  exact he.trans (map_zero _).symm

noncomputable def gradientIdeal (p : MvPolynomial ι K) : Ideal (MvPolynomial ι K) :=
  Ideal.span (Set.range fun i => pderiv i p)

omit [CharZero K] [Fintype ι] in
theorem pderiv_mem_gradientIdeal (p : MvPolynomial ι K) (i : ι) : pderiv i p ∈ gradientIdeal p :=
  Ideal.subset_span (Set.mem_range_self i)

theorem exists_annihilator (p : MvPolynomial ι K) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval p q ∈ (gradientIdeal p).radical := by
  classical
  let I := gradientIdeal p
  let S := I.minimalPrimes
  let : Fintype S := I.finite_minimalPrimes_of_isNoetherianRing.fintype
  have h (P : S) : ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval p q ∈ P.1 := by
    let : P.1.IsPrime := P.2.isPrime
    exact exists_mem_prime p P.1 (fun i => P.2.le (pderiv_mem_gradientIdeal p i))
  choose q hq hm using h
  refine ⟨∏ P : S, q P, Finset.prod_ne_zero_iff.mpr (fun P _ => hq P), ?_⟩
  change Polynomial.aeval p (∏ P : S, q P) ∈ I.radical
  rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
  intro P hP
  rw [map_prod]
  exact P.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨P, hP⟩ : S))) (hm ⟨P, hP⟩)

omit [CharZero K] [Fintype ι] in
theorem eval_annihilator (p : MvPolynomial ι K) (q : Polynomial K)
    (hq : Polynomial.aeval p q ∈ (gradientIdeal p).radical) (x : ι → K)
    (hx : ∀ i, MvPolynomial.aeval x (pderiv i p) = 0) : q.eval (MvPolynomial.aeval x p) = 0 := by
  have hI : gradientIdeal p ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hx i
  obtain ⟨n, hn⟩ := hq
  have he := hI hn
  change MvPolynomial.aeval x ((Polynomial.aeval p q) ^ n) = 0 at he
  rw [map_pow, ← Polynomial.aeval_algHom_apply] at he
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
    (eq_zero_of_pow_eq_zero he)

theorem finite_critical_values (p : MvPolynomial ι K) :
    {c : K | ∃ x : ι → K, (∀ i, MvPolynomial.aeval x (pderiv i p) = 0) ∧ MvPolynomial.aeval x p = c}.Finite := by
  obtain ⟨q, hq, hm⟩ := exists_annihilator p
  apply (Polynomial.finite_setOfPred_isRoot hq).subset
  rintro c ⟨x, hx, rfl⟩
  exact eval_annihilator p q hm x hx

end LeanCanny.Algebra.CriticalValueAnnihilator
