/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Pi

/-! # Finite zero sets from algebraic generic coordinates

If every coordinate is algebraic in the fraction field of each minimal-prime
quotient, it has a nonzero univariate annihilator modulo the radical ideal.
The zero set lies in a finite product of univariate root sets. This argument
provides no effective degree or coefficient bounds.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAlgebraicZeros
open MvPolynomial
open scoped BigOperators

variable {K ι : Type*} [Field K]

noncomputable def quotientPoint (P : Ideal (MvPolynomial ι K)) : ι → FractionRing (MvPolynomial ι K ⧸ P) :=
  fun i => algebraMap (MvPolynomial ι K ⧸ P) _ (Ideal.Quotient.mk P (X i))

theorem eval_quotientPoint (P : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    MvPolynomial.aeval (quotientPoint P) p =
      algebraMap (MvPolynomial ι K ⧸ P) _ (Ideal.Quotient.mk P p) := by
  let φ : MvPolynomial ι K →ₐ[K] FractionRing (MvPolynomial ι K ⧸ P) :=
    (IsScalarTower.toAlgHom K (MvPolynomial ι K ⧸ P) _).comp (Ideal.Quotient.mkₐ K P)
  have hφ : MvPolynomial.aeval (quotientPoint P) = φ := by
    ext i
    simp only [MvPolynomial.aeval_X, quotientPoint, φ, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom']
  exact congrArg (fun f : MvPolynomial ι K →ₐ[K] _ => f p) hφ

theorem exists_mem_prime (P : Ideal (MvPolynomial ι K)) [P.IsPrime] (i : ι)
    (hi : IsAlgebraic K (quotientPoint P i)) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval (X i : MvPolynomial ι K) q ∈ P := by
  obtain ⟨q, hq, heq⟩ := hi
  refine ⟨q, hq, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (IsFractionRing.injective (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)))
  rw [map_zero, ← eval_quotientPoint, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  exact heq

variable [Fintype ι]

theorem exists_coordinate_annihilator (I : Ideal (MvPolynomial ι K))
    (hcoords : ∀ P ∈ I.minimalPrimes, ∀ i, IsAlgebraic K (quotientPoint P i)) (i : ι) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval (X i : MvPolynomial ι K) q ∈ I.radical := by
  classical
  let S := I.minimalPrimes
  let : Fintype S := I.finite_minimalPrimes_of_isNoetherianRing.fintype
  have h (P : S) : ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval (X i : MvPolynomial ι K) q ∈ P.1 := by
    let : P.1.IsPrime := P.2.isPrime
    exact exists_mem_prime P.1 i (hcoords P.1 P.2 i)
  choose q hq hm using h
  refine ⟨∏ P : S, q P, Finset.prod_ne_zero_iff.mpr (fun P _ => hq P), ?_⟩
  rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
  intro P hP
  rw [map_prod]
  exact P.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨P, hP⟩ : S))) (hm ⟨P, hP⟩)

def zeroSet (I : Ideal (MvPolynomial ι K)) : Set (ι → K) :=
  {x | ∀ p ∈ I, MvPolynomial.aeval x p = 0}

omit [Fintype ι] in
theorem eval_coordinate_annihilator (I : Ideal (MvPolynomial ι K)) (i : ι) (q : Polynomial K)
    (hq : Polynomial.aeval (X i : MvPolynomial ι K) q ∈ I.radical)
    (x : ι → K) (hx : x ∈ zeroSet I) : q.eval (x i) = 0 := by
  obtain ⟨n, hn⟩ := hq
  have he := hx _ hn
  rw [map_pow, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X] at he
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using eq_zero_of_pow_eq_zero he

theorem finite_zeroSet (I : Ideal (MvPolynomial ι K))
    (hcoords : ∀ P ∈ I.minimalPrimes, ∀ i, IsAlgebraic K (quotientPoint P i)) :
    (zeroSet I).Finite := by
  choose q hq hm using exists_coordinate_annihilator I hcoords
  apply (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hq i))).subset
  intro x hx i
  exact eval_coordinate_annihilator I i (q i) (hm i) x hx

end LeanCanny.Algebra.FiniteAlgebraicZeros
