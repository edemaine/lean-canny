/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCoordinateSystem
public import LeanCanny.Algebra.BivariateCharacteristicBounds
public import LeanCanny.Algebra.MacaulayBivariateBounds

/-! # Coordinate-system budgets with a retained polynomial parameter

Homogenization and the extra coordinate row preserve the sweep-parameter
degree allowance. Total integer mass again gains only two bits. These
estimates bound the actual lowest Macaulay numerator in both variables.
-/

@[expose] public section

namespace LeanCanny.Algebra.AffineCoordinateSystem
open MvPolynomial
open scoped Classical

variable {n : ℕ} {R : Type*} [CommRing R]

theorem native_coefficient_inner_degree
    (q : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (coordinate : Fin n) (E : ℕ) (hq : ∀ j e, ((q j).coeff e).natDegree ≤ E)
    (j : Option (Fin n)) (e : Option (Fin n) →₀ ℕ) (k : ℕ) :
    (((nativeRow q d coordinate j).coeff e).coeff k).natDegree ≤ E := by
  cases j with
  | none =>
    rw [nativeRow, coeff_sub, C_mul_X_eq_monomial, coeff_monomial, coeff_X]
    split_ifs <;> simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one,
      Polynomial.coeff_zero] <;> (try split_ifs) <;> simp
  | some j =>
    rw [nativeRow, WeightedHomogenization.coefficient]
    split_ifs
    · rw [MvPolynomial.coeff_map, Polynomial.coeff_C]
      split_ifs
      · exact hq j _
      · simp
    · simp

theorem coefficient_inner_degree (q : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (coordinate : Fin n) (E : ℕ) (hq : ∀ j e, ((q j).coeff e).natDegree ≤ E)
    (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (((rows q d coordinate j).coeff e).coeff k).natDegree ≤ E := by
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rows, Fin.cons_zero, Fin.cons_succ, rename_coefficient] <;>
    exact native_coefficient_inner_degree q d coordinate E hq _ _ k

omit [CommRing R] in
theorem native_coefficient_nested_mass
    (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ)
    (coordinate : Fin n) (b : ℕ) (hq : ∀ j e, coefficientMass ((q j).coeff e) ≤ 2 ^ b)
    (j : Option (Fin n)) (e : Option (Fin n) →₀ ℕ) :
    NestedMass.mass ((nativeRow q d coordinate j).coeff e) ≤ 2 ^ (b + 2) := by
  have hpow : 2 ^ b ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  cases j with
  | none =>
    rw [nativeRow, coeff_sub, C_mul_X_eq_monomial, coeff_monomial, coeff_X]
    have hX : NestedMass.mass (Polynomial.X : Polynomial (Polynomial ℤ)) = 1 := by
      change NestedMass.mass (Polynomial.monomial 1 (Polynomial.C (1 : ℤ))) = 1
      rw [NestedMass.monomial, coefficientMass_C]
      rfl
    have h1 : NestedMass.mass (1 : Polynomial (Polynomial ℤ)) = 1 := by
      change NestedMass.mass (Polynomial.C (Polynomial.C (1 : ℤ))) = 1
      rw [NestedMass.C, coefficientMass_C]
      rfl
    apply (NestedMass.sub_le _ _).trans
    have hpos := Nat.one_le_two_pow (n := b)
    split_ifs <;> simp only [hX, h1, NestedMass.zero] <;> rw [pow_add] <;> omega
  | some j =>
    rw [nativeRow, WeightedHomogenization.coefficient]
    split_ifs
    · rw [MvPolynomial.coeff_map, NestedMass.C]
      exact (hq j _).trans hpow
    · simp

omit [CommRing R] in
theorem coefficient_nested_mass (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ)
    (coordinate : Fin n) (b : ℕ) (hq : ∀ j e, coefficientMass ((q j).coeff e) ≤ 2 ^ b)
    (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    NestedMass.mass ((rows q d coordinate j).coeff e) ≤ 2 ^ (b + 2) := by
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rows, Fin.cons_zero, Fin.cons_succ, rename_coefficient] <;>
    exact native_coefficient_nested_mass q d coordinate b hq _ _

end LeanCanny.Algebra.AffineCoordinateSystem

namespace LeanCanny.Algebra.Macaulay
open scoped Classical

theorem matrix_entry_nested_mass_le {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial ℤ))) (d : Fin n → ℕ) (W b : ℕ)
    (hp : ∀ i e, NestedMass.mass ((p i).coeff e) ≤ 2 ^ b) (r s : Index n W) :
    NestedMass.mass (matrix p d W r s) ≤ 2 ^ b := by
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · rw [entry_active p d W r s hr]
    split_ifs
    · exact hp _ _
    · simp
  · simp only [matrix, dite_eq_right hr, Matrix.one_apply]
    split_ifs
    · change NestedMass.mass (Polynomial.C (Polynomial.C (1 : ℤ))) ≤ 2 ^ b
      rw [NestedMass.C, coefficientMass_C]
      exact Nat.one_le_two_pow
    · simp

end LeanCanny.Algebra.Macaulay
