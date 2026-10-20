/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalRepresentationTransfer
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Integer polynomials for rational coordinate representations

Clear rational coefficients with a common nonzero integer scale for each
coordinate numerator/denominator pair. This preserves the represented rational
function, the parameter roots, denominator nonvanishing and polynomial degrees.
The construction supplies no effective coefficient-height or workspace bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerCoordinatePolynomials
open Polynomial

theorem exists_integer_scaling (p : ℚ[X]) :
    ∃ q : ℤ[X], ∃ m : ℤ, m ≠ 0 ∧ q.map (algebraMap ℤ ℚ) = C (m : ℚ) * p := by
  obtain ⟨m, hm, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) p, m, nonZeroDivisors.ne_zero hm, ?_⟩
  rw [← IsScalarTower.algebraMap_smul ℚ m p, Polynomial.smul_eq_C_mul] at he
  exact he

/-- The same integer multiple is used for both polynomials. -/
theorem exists_integer_pair (p q : ℚ[X]) :
    ∃ n d : ℤ[X], ∃ m : ℤ, m ≠ 0 ∧
      n.map (algebraMap ℤ ℚ) = C (m : ℚ) * p ∧ d.map (algebraMap ℤ ℚ) = C (m : ℚ) * q := by
  obtain ⟨n, a, ha, hn⟩ := exists_integer_scaling p
  obtain ⟨d, b, hb, hd⟩ := exists_integer_scaling q
  refine ⟨C b * n, C a * d, a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · simp only [Polynomial.map_mul, Polynomial.map_C, hn]
    change C (b : ℚ) * (C (a : ℚ) * p) = C ((a * b : ℤ) : ℚ) * p
    rw [Int.cast_mul, Polynomial.C_mul]
    ring
  · simp only [Polynomial.map_mul, Polynomial.map_C, hd]
    change C (a : ℚ) * (C (b : ℚ) * q) = C ((a * b : ℤ) : ℚ) * q
    rw [Int.cast_mul, Polynomial.C_mul, mul_assoc]

variable {ι τ : Type*} [Fintype ι] {p : τ → MvPolynomial ι ℚ}

/-- The map identities record the common scale needed to preserve coordinate ratios. -/
structure IntegerData (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p) where
  polynomial : ℤ[X]
  numerator : ι → ℤ[X]
  denominator : ι → ℤ[X]
  polynomial_scale : ℤ
  coordinate_scale : ι → ℤ
  polynomial_scale_ne_zero : polynomial_scale ≠ 0
  coordinate_scale_ne_zero : ∀ j, coordinate_scale j ≠ 0
  map_polynomial : polynomial.map (algebraMap ℤ ℚ) = C (polynomial_scale : ℚ) * r.polynomial
  map_numerator : ∀ j, (numerator j).map (algebraMap ℤ ℚ) = C (coordinate_scale j : ℚ) * r.numerator j
  map_denominator : ∀ j, (denominator j).map (algebraMap ℤ ℚ) = C (coordinate_scale j : ℚ) * r.denominator j

theorem nonempty_integerData (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p) :
    Nonempty (IntegerData r) := by
  obtain ⟨q, m, hm, hq⟩ := exists_integer_scaling r.polynomial
  choose n d s hs hn hd using fun j => exists_integer_pair (r.numerator j) (r.denominator j)
  exact ⟨⟨q, n, d, m, s, hm, hs, hq, hn, hd⟩⟩

omit [Fintype ι] in
private theorem degree_eq_of_map_scaling (q : ℤ[X]) (p : ℚ[X]) (m : ℤ) (hm : m ≠ 0)
    (he : q.map (algebraMap ℤ ℚ) = C (m : ℚ) * p) : q.natDegree = p.natDegree := by
  have hinj : Function.Injective (algebraMap ℤ ℚ) := Int.cast_injective
  rw [← Polynomial.natDegree_map_eq_of_injective hinj q, he,
    Polynomial.natDegree_C_mul (Int.cast_ne_zero.mpr hm)]

namespace IntegerData
variable {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p}

theorem polynomial_natDegree (c : IntegerData r) : c.polynomial.natDegree = r.polynomial.natDegree :=
  degree_eq_of_map_scaling _ _ _ c.polynomial_scale_ne_zero c.map_polynomial

theorem numerator_natDegree (c : IntegerData r) (j : ι) : (c.numerator j).natDegree = (r.numerator j).natDegree :=
  degree_eq_of_map_scaling _ _ _ (c.coordinate_scale_ne_zero j) (c.map_numerator j)

theorem denominator_natDegree (c : IntegerData r) (j : ι) : (c.denominator j).natDegree = (r.denominator j).natDegree :=
  degree_eq_of_map_scaling _ _ _ (c.coordinate_scale_ne_zero j) (c.map_denominator j)

theorem polynomial_separable (c : IntegerData r) : (c.polynomial.map (algebraMap ℤ ℚ)).Separable := by
  rw [c.map_polynomial]
  exact Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (Int.cast_ne_zero.mpr c.polynomial_scale_ne_zero))) r.separable

section Extension
variable {E : Type*} [Field E] [Algebra ℚ E]

omit [Fintype ι] in
private theorem intCast_ne_zero (m : ℤ) (hm : m ≠ 0) : (m : E) ≠ 0 := by
  have hn : (algebraMap ℚ E) (m : ℚ) ≠ 0 := by
    intro hz
    exact (Int.cast_ne_zero.mpr hm : (m : ℚ) ≠ 0)
      ((algebraMap ℚ E).injective (hz.trans (map_zero _).symm))
  simpa using hn

omit [Fintype ι] in
private theorem aeval_of_map_scaling (q : ℤ[X]) (p : ℚ[X]) (m : ℤ)
    (he : q.map (algebraMap ℤ ℚ) = C (m : ℚ) * p) (θ : E) :
    Polynomial.aeval θ q = (m : E) * Polynomial.aeval θ p := by
  calc
    Polynomial.aeval θ q = Polynomial.aeval θ (q.map (algebraMap ℤ ℚ)) :=
      Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℤ ℚ E).symm q θ
    _ = (m : E) * Polynomial.aeval θ p := by rw [he]; simp

theorem aeval_polynomial (c : IntegerData r) (θ : E) :
    Polynomial.aeval θ c.polynomial = (c.polynomial_scale : E) * Polynomial.aeval θ r.polynomial :=
  aeval_of_map_scaling _ _ _ c.map_polynomial θ

theorem aeval_numerator (c : IntegerData r) (θ : E) (j : ι) :
    Polynomial.aeval θ (c.numerator j) = (c.coordinate_scale j : E) * Polynomial.aeval θ (r.numerator j) :=
  aeval_of_map_scaling _ _ _ (c.map_numerator j) θ

theorem aeval_denominator (c : IntegerData r) (θ : E) (j : ι) :
    Polynomial.aeval θ (c.denominator j) = (c.coordinate_scale j : E) * Polynomial.aeval θ (r.denominator j) :=
  aeval_of_map_scaling _ _ _ (c.map_denominator j) θ

theorem root_iff (c : IntegerData r) (θ : E) :
    Polynomial.aeval θ c.polynomial = 0 ↔ Polynomial.aeval θ r.polynomial = 0 := by
  rw [c.aeval_polynomial]
  exact mul_eq_zero.trans (or_iff_right (intCast_ne_zero (E := E) _ c.polynomial_scale_ne_zero))

theorem denominator_ne_zero_iff (c : IntegerData r) (θ : E) (j : ι) :
    Polynomial.aeval θ (c.denominator j) ≠ 0 ↔ Polynomial.aeval θ (r.denominator j) ≠ 0 := by
  rw [c.aeval_denominator]
  exact ⟨fun h => (mul_ne_zero_iff.mp h).2,
    fun h => mul_ne_zero (intCast_ne_zero (E := E) _ (c.coordinate_scale_ne_zero j)) h⟩

noncomputable def decode (c : IntegerData r) (θ : E) : ι → E := fun j =>
  Polynomial.aeval θ (c.numerator j) / Polynomial.aeval θ (c.denominator j)

theorem decode_eq (c : IntegerData r) (θ : E) : c.decode θ = r.decodeOver θ := by
  funext j
  change Polynomial.aeval θ (c.numerator j) / Polynomial.aeval θ (c.denominator j) = _
  rw [c.aeval_numerator, c.aeval_denominator]
  exact mul_div_mul_left _ _ (intCast_ne_zero (E := E) _ (c.coordinate_scale_ne_zero j))

theorem denominator_ne_zero_at_root (c : IntegerData r) (θ : E)
    (hθ : Polynomial.aeval θ c.polynomial = 0) (j : ι) :
    Polynomial.aeval θ (c.denominator j) ≠ 0 :=
  (c.denominator_ne_zero_iff θ j).mpr ((r.decodeOver_sound θ ((c.root_iff θ).mp hθ)).2.2 j)

noncomputable def rootEquiv (c : IntegerData r) :
    {θ : E // Polynomial.aeval θ c.polynomial = 0} ≃ {θ : E // Polynomial.aeval θ r.polynomial = 0} where
  toFun θ := ⟨θ.val, (c.root_iff θ.val).mp θ.property⟩
  invFun θ := ⟨θ.val, (c.root_iff θ.val).mpr θ.property⟩
  left_inv _θ := rfl
  right_inv _θ := rfl

end Extension
end IntegerData
end LeanCanny.Algebra.IntegerCoordinatePolynomials
