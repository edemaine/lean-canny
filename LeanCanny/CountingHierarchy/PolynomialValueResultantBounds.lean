/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialValueResultant
public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.Algebra.CoefficientBounds

/-! # Effective degree and mass bounds for algebraic test-value annihilators -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped Classical

private theorem value_shift_coefficient_degree (g : Polynomial ℤ) (i : ℕ) :
    ((Polynomial.C Polynomial.X - g.map Polynomial.C).coeff i).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le _ (by simp)
  by_cases hi : i = 0 <;> simp [Polynomial.coeff_C, hi]

private theorem value_shift_coefficient_mass (g : Polynomial ℤ) (i : ℕ) :
    coefficientMass ((Polynomial.C Polynomial.X - g.map Polynomial.C).coeff i) ≤ 1 + coefficientMass g := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map]
  apply (coefficientMass_sub_le _ _).trans
  apply Nat.add_le_add _ (by simpa only [coefficientMass_C] using coeff_natAbs_le_coefficientMass g i)
  by_cases hi : i = 0
  · subst i
    rw [Polynomial.coeff_C_zero]
    change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) ≤ 1
    rw [coefficientMass_monomial]
    exact Nat.le_refl _
  · simp only [Polynomial.coeff_C, hi, ite_false, coefficientMass_zero, Nat.zero_le]

theorem polynomialValueResultant_natDegree_le (p g : Polynomial ℤ) :
    (polynomialValueResultant p g).natDegree ≤ p.natDegree := by
  have h := resultant_natDegree_le (p.map Polynomial.C)
    (Polynomial.C Polynomial.X - g.map Polynomial.C)
    (p.map Polynomial.C).natDegree (Polynomial.C Polynomial.X - g.map Polynomial.C).natDegree 0 1
    (by intro i; simp only [Polynomial.coeff_map, Polynomial.natDegree_C, le_refl])
    (value_shift_coefficient_degree g)
  simpa only [polynomialValueResultant, Nat.mul_one, Nat.mul_zero, Nat.add_zero,
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective] using h

/-- The size of the Sylvester matrix and all its column budgets are short. -/
@[expose] def polynomialValueMassExponent (D E bp bg : ℕ) : ℕ :=
  (D + E).size * (D + E) + (D + E) * (bp + bg + 1)

theorem polynomialValueResultant_mass_le (p g : Polynomial ℤ) (D E bp bg : ℕ)
    (hD : p.natDegree ≤ D) (hE : g.natDegree ≤ E)
    (hp : coefficientMass p ≤ 2 ^ bp) (hg : coefficientMass g ≤ 2 ^ bg) :
    coefficientMass (polynomialValueResultant p g) ≤ 2 ^ polynomialValueMassExponent D E bp bg := by
  let f := p.map Polynomial.C
  let q := Polynomial.C Polynomial.X - g.map Polynomial.C
  have hfirst (i : ℕ) : coefficientMass (f.coeff i) ≤ 2 ^ (bp + bg + 1) := by
    apply (show coefficientMass (f.coeff i) ≤ 2 ^ bp from by
      simpa only [f, Polynomial.coeff_map, coefficientMass_C] using
        (coeff_natAbs_le_coefficientMass p i).trans hp).trans
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsecond (i : ℕ) : coefficientMass (q.coeff i) ≤ 2 ^ (bp + bg + 1) := by
    apply (value_shift_coefficient_mass g i).trans
    have hb : 1 + coefficientMass g ≤ 2 ^ (bg + 1) := by
      have := Nat.one_le_two_pow (n := bg)
      rw [pow_succ]
      omega
    exact hb.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have he (i j : Fin (f.natDegree + q.natDegree)) :
      coefficientMass (Polynomial.sylvester f q f.natDegree q.natDegree i j) ≤ 2 ^ (bp + bg + 1) := by
    induction j using Fin.addCases <;> simp only [Polynomial.sylvester, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · exact hsecond _
      · simp
    · split_ifs
      · exact hfirst _
      · simp
  have hfdeg : f.natDegree ≤ D := by
    exact (Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective p).le.trans hD
  have hqdeg : q.natDegree ≤ E := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (by simpa only [Polynomial.natDegree_C] using Nat.zero_le E)
      (Polynomial.natDegree_map_le.trans hE)
  have hN := Nat.add_le_add hfdeg hqdeg
  apply (det_coefficientMass_le_pow _ _ he).trans
  simp only [Fintype.card_fin]
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hN) hN)
    (Nat.mul_le_mul_right _ hN)

end LeanCanny.CountingHierarchy
