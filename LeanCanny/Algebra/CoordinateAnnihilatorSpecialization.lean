/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteFiberSpecialization

/-! # Coordinate annihilators preserved in every extension field

Retain the cleared coordinate polynomials and radical-ideal identities used by
finite-fiber specialization. Outside their exceptional factor, specialization
gives nonzero polynomials over the specialized coefficient field annihilating
every solution coordinate in any extension of that field. Thus all such
coordinates are algebraic over the specialized field. No effective bounds on
the certificate polynomials are supplied.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoordinateAnnihilatorSpecialization
open MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A ι : Type*} [CommRing A]

structure Certificate (I : Ideal (MvPolynomial ι A)) where
  polynomial : ι → Polynomial A
  factor : ι → A
  polynomial_ne_zero : ∀ i, polynomial i ≠ 0
  factor_ne_zero : ∀ i, factor i ≠ 0
  radical_mem : ∀ i, C (factor i) * Polynomial.aeval (X i : MvPolynomial ι A) (polynomial i) ∈ I.radical

section Construction
variable [IsDomain A] [Fintype ι]
variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]

theorem nonempty_certificate (I : Ideal (MvPolynomial ι A))
    (hcoords : ∀ P ∈ (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))).minimalPrimes,
      ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i)) : Nonempty (Certificate I) := by
  choose q hq hm using FiniteAlgebraicZeros.exists_coordinate_annihilator
    (I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F))) hcoords
  have h (i : ι) := FiniteFiberSpecialization.exists_cleared_annihilator I i (q i) (hq i) (hm i)
  choose Q hQ s hs hsI using h
  exact ⟨⟨Q, s, hQ, hs, hsI⟩⟩

end Construction

namespace Certificate
variable {I : Ideal (MvPolynomial ι A)} [Fintype ι]

noncomputable def exceptional (c : Certificate I) : A := ∏ i, c.factor i * (c.polynomial i).leadingCoeff

theorem exceptional_ne_zero [IsDomain A] (c : Certificate I) : c.exceptional ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ =>
    mul_ne_zero (c.factor_ne_zero i) (Polynomial.leadingCoeff_ne_zero.mpr (c.polynomial_ne_zero i)))

variable {K : Type*} [Field K]

theorem specialized_factors_ne_zero (c : Certificate I) (φ : A →+* K) (hφ : φ c.exceptional ≠ 0) (i : ι) :
    φ (c.factor i) ≠ 0 ∧ φ (c.polynomial i).leadingCoeff ≠ 0 := by
  have hp : ∏ j, φ (c.factor j * (c.polynomial j).leadingCoeff) ≠ 0 := by
    simpa only [exceptional, map_prod] using hφ
  have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  rw [map_mul] at hi
  exact mul_ne_zero_iff.mp hi

theorem specialized_polynomial_ne_zero (c : Certificate I) (φ : A →+* K) (hφ : φ c.exceptional ≠ 0) (i : ι) :
    (c.polynomial i).map φ ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  simpa only [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ (c.specialized_factors_ne_zero φ hφ i).2] using
    (c.specialized_factors_ne_zero φ hφ i).2

/-- The annihilators remain over K even when the solution lies in a larger E. -/
theorem aeval_specialized_eq_zero {E : Type*} [Field E] [Algebra K E]
    (c : Certificate I) (φ : A →+* K) (hφ : φ c.exceptional ≠ 0)
    (x : ι → E) (hx : ∀ p ∈ I, p.eval₂ ((algebraMap K E).comp φ) x = 0) (i : ι) :
    Polynomial.aeval (x i) ((c.polynomial i).map φ) = 0 := by
  obtain ⟨n, hn⟩ := c.radical_mem i
  have he := hx _ hn
  rw [MvPolynomial.eval₂_pow] at he
  have hz := eq_zero_of_pow_eq_zero he
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, FiniteFiberSpecialization.eval_coordinate_aeval] at hz
  have hfac : ((algebraMap K E).comp φ) (c.factor i) ≠ 0 := by
    exact fun h => (c.specialized_factors_ne_zero φ hφ i).1
      ((algebraMap K E).injective (h.trans (map_zero _).symm))
  have hroot := (mul_eq_zero.mp hz).resolve_left hfac
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact hroot

theorem algebraic_coordinates {E : Type*} [Field E] [Algebra K E]
    (c : Certificate I) (φ : A →+* K) (hφ : φ c.exceptional ≠ 0)
    (x : ι → E) (hx : ∀ p ∈ I, p.eval₂ ((algebraMap K E).comp φ) x = 0) :
    ∀ i, IsAlgebraic K (x i) := fun i =>
  ⟨(c.polynomial i).map φ, c.specialized_polynomial_ne_zero φ hφ i,
    c.aeval_specialized_eq_zero φ hφ x hx i⟩

theorem finite_solutions {E : Type*} [Field E] [Algebra K E]
    (c : Certificate I) (φ : A →+* K) (hφ : φ c.exceptional ≠ 0) :
    {x : ι → E | ∀ p ∈ I, p.eval₂ ((algebraMap K E).comp φ) x = 0}.Finite := by
  have hne (i : ι) : ((c.polynomial i).map φ).map (algebraMap K E) ≠ 0 :=
    Polynomial.map_ne_zero (c.specialized_polynomial_ne_zero φ hφ i)
  apply (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hne i))).subset
  intro x hx i
  change Polynomial.eval (x i) (((c.polynomial i).map φ).map (algebraMap K E)) = 0
  rw [Polynomial.eval_map_algebraMap]
  exact c.aeval_specialized_eq_zero φ hφ x hx i

end Certificate
end LeanCanny.Algebra.CoordinateAnnihilatorSpecialization
