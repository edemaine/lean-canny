/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialValueResultantBounds
public import LeanCanny.CountingHierarchy.LargeSpecializationBounds
public import Mathlib.Algebra.Polynomial.Reverse

/-! # Uniform dyadic bounds for nonzero test values at real algebraic roots -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

theorem polynomialValueResultant_real_root (p g : Polynomial ℤ) (hp : p ≠ 0) (a : ℝ)
    (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) :
    (polynomialValueResultant p g).eval₂ (Int.castRingHom ℝ)
      (g.eval₂ (Int.castRingHom ℝ) a) = 0 := by
  have hcp := Polynomial.ringHom_eval₂_intCastRingHom p Complex.ofRealHom a
  simp only [Complex.ofRealHom_eq_coe] at hcp
  have haC : p.eval₂ (Int.castRingHom ℂ) (a : ℂ) = 0 := by
    rw [← hcp, ha, Complex.ofReal_zero]
  have hroot := polynomialValueResultant_root p g hp (a : ℂ) haC
  have hcg := Polynomial.ringHom_eval₂_intCastRingHom g Complex.ofRealHom a
  have hcr := Polynomial.ringHom_eval₂_intCastRingHom (polynomialValueResultant p g)
    Complex.ofRealHom (g.eval₂ (Int.castRingHom ℝ) a)
  simp only [Complex.ofRealHom_eq_coe] at hcg hcr
  rw [← hcg, ← hcr] at hroot
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_zero] using hroot

/-- A real evaluation is bounded by coefficient mass times an advertised
 absolute radius raised to an advertised degree. -/
theorem abs_eval₂_le_mass_radius (g : Polynomial ℤ) (E : ℕ) (hE : g.natDegree ≤ E)
    (a R : ℝ) (hR : 1 ≤ R) (ha : |a| ≤ R) :
    |g.eval₂ (Int.castRingHom ℝ) a| ≤ (coefficientMass g : ℝ) * R ^ E := by
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, Int.coe_castRingHom]
  calc
    _ ≤ ∑ i ∈ g.support, |(g.coeff i : ℝ) * a ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ g.support, |(g.coeff i : ℝ)| * R ^ E := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (abs_nonneg _) ha i).trans
        (pow_le_pow_right₀ hR ((Polynomial.le_natDegree_of_mem_supp i hi).trans hE))
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [coefficientMass, Polynomial.sum, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]

/-- Precision for the reciprocal-root lower bound. -/
@[expose] def algebraicTestLowerPrecision (D E bp bg : ℕ) : ℕ :=
  polynomialValueMassExponent D E bp bg + (D + 1).size + 1

theorem nonzero_test_value_lower_bound (p g : Polynomial ℤ) (hp : p ≠ 0)
    (D E bp bg : ℕ) (hD : p.natDegree ≤ D) (hE : g.natDegree ≤ E)
    (hpm : coefficientMass p ≤ 2 ^ bp) (hgm : coefficientMass g ≤ 2 ^ bg)
    (a : ℝ) (ha : p.eval₂ (Int.castRingHom ℝ) a = 0)
    (hne : g.eval₂ (Int.castRingHom ℝ) a ≠ 0) :
    ((2 : ℝ) ^ algebraicTestLowerPrecision D E bp bg)⁻¹ <
      |g.eval₂ (Int.castRingHom ℝ) a| := by
  let F := polynomialValueResultant p g
  let v := g.eval₂ (Int.castRingHom ℝ) a
  let := invertibleOfNonzero hne
  have hv : F.reverse.eval₂ (Int.castRingHom ℝ) v⁻¹ = 0 := by
    simpa only [invOf_eq_inv] using
      (Polynomial.eval₂_reverse_eq_zero_iff (Int.castRingHom ℝ) v F).mpr
        (polynomialValueResultant_real_root p g hp a ha)
  have hF : F ≠ 0 := polynomialValueResultant_ne_zero p g hp
  have hmass : coefficientMass F.reverse ≤
      2 ^ (polynomialValueMassExponent D E bp bg + (D + 1).size) := by
    apply coefficientMass_le_pow_of_degree_coeff F.reverse D _
      ((Polynomial.reverse_natDegree_le F).trans ((polynomialValueResultant_natDegree_le p g).trans hD))
    intro i
    rw [Polynomial.coeff_reverse]
    exact (coeff_natAbs_le_coefficientMass F _).trans
      (polynomialValueResultant_mass_le p g D E bp bg hD hE hpm hgm)
  have hbound := abs_root_lt_coefficientMass_add_one F.reverse
    (Polynomial.reverse_eq_zero.not.mpr hF) v⁻¹ hv
  have hpow : (coefficientMass F.reverse : ℝ) + 1 ≤
      (2 : ℝ) ^ algebraicTestLowerPrecision D E bp bg :=
    cast_add_one_le_pow hmass le_rfl
  have hinv : |v|⁻¹ < (2 : ℝ) ^ algebraicTestLowerPrecision D E bp bg := by
    simpa only [abs_inv] using hbound.trans_le hpow
  exact (inv_lt_comm₀ (abs_pos.mpr hne) (pow_pos (by norm_num) _)).mp hinv

theorem test_value_upper_bound (p g : Polynomial ℤ) (hp : p ≠ 0)
    (E bp bg : ℕ) (hE : g.natDegree ≤ E)
    (hpm : coefficientMass p ≤ 2 ^ bp) (hgm : coefficientMass g ≤ 2 ^ bg)
    (a : ℝ) (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) :
    |g.eval₂ (Int.castRingHom ℝ) a| ≤ (2 : ℝ) ^ (bg + E * (bp + 1)) := by
  have hroot := abs_root_lt_coefficientMass_add_one p hp a ha
  have hR : |a| ≤ (2 : ℝ) ^ (bp + 1) :=
    hroot.le.trans (cast_add_one_le_pow hpm le_rfl)
  have hg : (coefficientMass g : ℝ) ≤ (2 : ℝ) ^ bg := by exact_mod_cast hgm
  apply (abs_eval₂_le_mass_radius g E hE a ((2 : ℝ) ^ (bp + 1))
    (one_le_pow₀ (by norm_num)) hR).trans
  exact (mul_le_mul_of_nonneg_right hg (by positivity)).trans_eq (by
    rw [← pow_mul, ← pow_add, Nat.mul_comm E])

/-- One short precision suffices for both upper and nonzero lower bounds. -/
@[expose] def algebraicTestPrecision (D E bp bg : ℕ) : ℕ :=
  algebraicTestLowerPrecision D E bp bg + (bg + E * (bp + 1))

/-- Nonmonic and repeated-root source polynomials are included; zero test
 values are retained as a separate, exact alternative. -/
theorem algebraic_test_value_range (p g : Polynomial ℤ) (hp : p ≠ 0)
    (D E bp bg : ℕ) (hD : p.natDegree ≤ D) (hE : g.natDegree ≤ E)
    (hpm : coefficientMass p ≤ 2 ^ bp) (hgm : coefficientMass g ≤ 2 ^ bg)
    (a : ℝ) (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) :
    g.eval₂ (Int.castRingHom ℝ) a = 0 ∨
      (((2 : ℝ) ^ algebraicTestPrecision D E bp bg)⁻¹ ≤ |g.eval₂ (Int.castRingHom ℝ) a| ∧
        |g.eval₂ (Int.castRingHom ℝ) a| ≤ (2 : ℝ) ^ algebraicTestPrecision D E bp bg) := by
  by_cases hn : g.eval₂ (Int.castRingHom ℝ) a = 0
  · exact Or.inl hn
  · right
    constructor
    · have hlo := nonzero_test_value_lower_bound p g hp D E bp bg hD hE hpm hgm a ha hn
      apply le_trans _ hlo.le
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
    · apply (test_value_upper_bound p g hp E bp bg hE hpm hgm a ha).trans
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_left _ _)

end LeanCanny.CountingHierarchy
