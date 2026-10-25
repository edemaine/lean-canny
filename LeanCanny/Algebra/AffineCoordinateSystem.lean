/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationLayout
public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Homogeneous systems eliminating an affine root coordinate

Homogenize a square affine system, retaining `u` in the coefficient ring,
and add `u X₀-Xᵢ`. All coefficients have degree at most one in `u`.
For integer input the coefficient-mass allowance increases by two bits.
-/

@[expose] public section

namespace LeanCanny.Algebra.AffineCoordinateSystem
open MvPolynomial
open scoped Classical

variable {n : ℕ} {R : Type*} [CommRing R]

def layout : Option (Fin n) ≃ Fin (n + 1) := HomogenizationLayout.variableEquiv (Equiv.refl _)

noncomputable def nativeRow (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) : Option (Fin n) → MvPolynomial (Option (Fin n)) (Polynomial R)
  | none => C Polynomial.X * X none - X (some coordinate)
  | some j => WeightedHomogenization.homogenize (fun _ => 1) (d j) ((q j).map Polynomial.C)

noncomputable def rows (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial R) :=
  Fin.cons (rename layout (nativeRow q d coordinate none))
    (fun j => rename layout (nativeRow q d coordinate (some j)))

def degrees (d : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons 1 d

theorem homogeneous (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) (j : Fin (n + 1)) :
    (rows q d coordinate j).IsHomogeneous (degrees d j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · apply IsHomogeneous.rename_isHomogeneous
    exact ((isHomogeneous_X (Polynomial R) none).C_mul Polynomial.X).sub
      (isHomogeneous_X (Polynomial R) (some coordinate))
  · have hw : WeightedHomogenization.weights (fun _ : Fin n => 1) = 1 := by
      funext i
      cases i <;> rfl
    have h := WeightedHomogenization.homogeneous (fun _ : Fin n => 1) (d j) ((q j).map Polynomial.C)
    exact (show (nativeRow q d coordinate (some j)).IsHomogeneous (d j) by
      simpa only [nativeRow, MvPolynomial.IsHomogeneous, hw] using h).rename_isHomogeneous

theorem degrees_pos (d : Fin n → ℕ) (hd : ∀ j, 0 < d j) (j : Fin (n + 1)) :
    0 < degrees d j := by
  refine Fin.cases (by change 0 < (1 : ℕ); decide) (fun j => hd j) j

theorem rename_coefficient (p : MvPolynomial (Option (Fin n)) (Polynomial R))
    (e : Fin (n + 1) →₀ ℕ) :
    (rename layout p).coeff e = p.coeff (e.mapDomain layout.symm) := by
  have he : e = (e.mapDomain layout.symm).mapDomain layout := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  conv_lhs => rw [he]
  rw [MvPolynomial.coeff_rename_mapDomain layout layout.injective]

theorem native_coefficient_degree (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) (j : Option (Fin n)) (e : Option (Fin n) →₀ ℕ) :
    ((nativeRow q d coordinate j).coeff e).natDegree ≤ 1 := by
  cases j with
  | none =>
    rw [nativeRow, coeff_sub, C_mul_X_eq_monomial, coeff_monomial, coeff_X]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · split_ifs
      · exact Polynomial.natDegree_X_le
      · simp
    · split_ifs <;> simp
  | some j =>
    rw [nativeRow, WeightedHomogenization.coefficient]
    split_ifs <;> simp [MvPolynomial.coeff_map]

theorem coefficient_degree (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    ((rows q d coordinate j).coeff e).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rows, Fin.cons_zero, Fin.cons_succ, rename_coefficient] <;>
    exact native_coefficient_degree q d coordinate _ _

omit [CommRing R] in
theorem native_coefficient_mass (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (coordinate : Fin n) (b : ℕ) (hq : ∀ j e, ((q j).coeff e).natAbs ≤ 2 ^ b)
    (j : Option (Fin n)) (e : Option (Fin n) →₀ ℕ) :
    coefficientMass ((nativeRow q d coordinate j).coeff e) ≤ 2 ^ (b + 2) := by
  have hpow : 2 ^ b ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  cases j with
  | none =>
    rw [nativeRow, coeff_sub, C_mul_X_eq_monomial, coeff_monomial, coeff_X]
    have hX : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
      change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) = 1
      rw [coefficientMass_monomial]
      rfl
    have h1 : coefficientMass (1 : Polynomial ℤ) = 1 := by
      change coefficientMass (Polynomial.C (1 : ℤ)) = 1
      rw [coefficientMass_C]
      rfl
    apply (coefficientMass_sub_le _ _).trans
    have hpos := Nat.one_le_two_pow (n := b)
    split_ifs <;> simp only [hX, h1, coefficientMass_zero] <;> rw [pow_add] <;> omega
  | some j =>
    rw [nativeRow, WeightedHomogenization.coefficient]
    split_ifs
    · rw [MvPolynomial.coeff_map, coefficientMass_C]
      exact (hq j _).trans hpow
    · simp

omit [CommRing R] in
theorem coefficient_mass (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (coordinate : Fin n) (b : ℕ) (hq : ∀ j e, ((q j).coeff e).natAbs ≤ 2 ^ b)
    (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    coefficientMass ((rows q d coordinate j).coeff e) ≤ 2 ^ (b + 2) := by
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rows, Fin.cons_zero, Fin.cons_succ, rename_coefficient] <;>
    exact native_coefficient_mass q d coordinate b hq _ _

end LeanCanny.Algebra.AffineCoordinateSystem
