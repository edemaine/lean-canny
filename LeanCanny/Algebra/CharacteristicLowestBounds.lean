/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicQuotientDegree
public import LeanCanny.Algebra.CharacteristicCoefficientDegree
public import LeanCanny.Algebra.NestedCoefficientMass

/-! # Explicit budgets for lowest characteristic coefficients

The lowest coefficient of `det(A-sI)` is nonzero over a domain. If the entries
are polynomials in a retained parameter, its degree is at most matrix size
times entry degree. Integer coefficient sizes follow directly from the
determinant mass bound, avoiding bounds for a polynomial quotient.
-/

@[expose] public section

namespace LeanCanny.Algebra.CharacteristicLowestBounds
open Polynomial
open scoped BigOperators Classical

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

noncomputable def lowest (A : Matrix ι ι (Polynomial R)) : Polynomial R :=
  (AffineCharacteristic.subtractiveMatrix A).det.trailingCoeff

theorem lowest_ne_zero [IsDomain R] (A : Matrix ι ι (Polynomial R)) : lowest A ≠ 0 :=
  Polynomial.trailingCoeff_ne_zero.mpr (AffineCharacteristic.subtractive_det_ne_zero A)

theorem coefficient_degree_le (A : Matrix ι ι (Polynomial R)) (E : ℕ)
    (hA : ∀ r s, (A r s).natDegree ≤ E) (k : ℕ) :
    ((AffineCharacteristic.subtractiveMatrix A).det.coeff k).natDegree ≤ Fintype.card ι * E :=
  AffineCharacteristic.subtractive_det_coefficient_degree A E hA k

theorem degree_le (A : Matrix ι ι (Polynomial R)) (E : ℕ)
    (hA : ∀ r s, (A r s).natDegree ≤ E) :
    (lowest A).natDegree ≤ Fintype.card ι * E := coefficient_degree_le A E hA _

omit [CommRing R] [Fintype ι] in
theorem entry_mass (A : Matrix ι ι (Polynomial ℤ)) (M : ℕ)
    (hA : ∀ r s, coefficientMass (A r s) ≤ M) (r s : ι) :
    NestedMass.mass (AffineCharacteristic.subtractiveMatrix A r s) ≤ M + 1 := by
  have hdelta : coefficientMass ((1 : Matrix ι ι (Polynomial ℤ)) r s) ≤ 1 := by
    by_cases hrs : r = s
    · simp only [Matrix.one_apply, ite_eq_left hrs]
      change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 1
      rw [coefficientMass_C]
      decide
    · simp only [Matrix.one_apply, ite_eq_right hrs, coefficientMass_zero]
      exact Nat.zero_le _
  have hX : NestedMass.mass (Polynomial.X * Polynomial.C ((1 : Matrix ι ι (Polynomial ℤ)) r s)) =
      coefficientMass ((1 : Matrix ι ι (Polynomial ℤ)) r s) := by
    rw [show Polynomial.X * Polynomial.C ((1 : Matrix ι ι (Polynomial ℤ)) r s) =
      Polynomial.monomial 1 ((1 : Matrix ι ι (Polynomial ℤ)) r s) by
        rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial]]
    exact NestedMass.monomial _ _
  exact (NestedMass.sub_le _ _).trans (by
    rw [NestedMass.C, hX]
    exact Nat.add_le_add (hA r s) hdelta)

omit [CommRing R] in
theorem coefficient_mass_le (A : Matrix ι ι (Polynomial ℤ)) (M : ℕ)
    (hA : ∀ r s, coefficientMass (A r s) ≤ M) (j : ℕ) :
    coefficientMass ((AffineCharacteristic.subtractiveMatrix A).det.coeff j) ≤
      (Fintype.card ι).factorial * (M + 1) ^ Fintype.card ι :=
  (NestedMass.coeff_le _ _).trans
    (NestedMass.det_le (AffineCharacteristic.subtractiveMatrix A) (M + 1) (entry_mass A M hA))

omit [CommRing R] in
theorem mass_le (A : Matrix ι ι (Polynomial ℤ)) (M : ℕ)
    (hA : ∀ r s, coefficientMass (A r s) ≤ M) :
    coefficientMass (lowest A) ≤ (Fintype.card ι).factorial * (M + 1) ^ Fintype.card ι :=
  coefficient_mass_le A M hA _

omit [CommRing R] in
theorem all_coefficient_size_le (A : Matrix ι ι (Polynomial ℤ)) (b : ℕ)
    (hA : ∀ r s, coefficientMass (A r s) ≤ 2 ^ b) (j k : ℕ) :
    (((AffineCharacteristic.subtractiveMatrix A).det.coeff j).coeff k).natAbs.size ≤
      (Fintype.card ι).size * Fintype.card ι + Fintype.card ι * (b + 1) + 1 := by
  let N := Fintype.card ι
  have hfac : N.factorial ≤ 2 ^ (N.size * N) :=
    (Nat.factorial_le_pow N).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self N).le N).trans_eq (pow_mul _ _ _).symm)
  have hentry : 2 ^ b + 1 ≤ 2 ^ (b + 1) := by
    have hpos := Nat.one_le_two_pow (n := b)
    rw [pow_succ]
    omega
  have hbound : (((AffineCharacteristic.subtractiveMatrix A).det.coeff j).coeff k).natAbs ≤
      2 ^ (N.size * N + N * (b + 1)) := by
    calc
      _ ≤ coefficientMass ((AffineCharacteristic.subtractiveMatrix A).det.coeff j) :=
        coeff_natAbs_le_coefficientMass _ _
      _ ≤ N.factorial * (2 ^ b + 1) ^ N := coefficient_mass_le A (2 ^ b) hA j
      _ ≤ 2 ^ (N.size * N) * (2 ^ (b + 1)) ^ N :=
        Nat.mul_le_mul hfac (Nat.pow_le_pow_left hentry N)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm (b + 1)]
  simpa only [Nat.size_pow] using Nat.size_le_size hbound

omit [CommRing R] in
theorem coefficient_size_le (A : Matrix ι ι (Polynomial ℤ)) (b : ℕ)
    (hA : ∀ r s, coefficientMass (A r s) ≤ 2 ^ b) (k : ℕ) :
    ((lowest A).coeff k).natAbs.size ≤
      (Fintype.card ι).size * Fintype.card ι + Fintype.card ι * (b + 1) + 1 :=
  all_coefficient_size_le A b hA _ k

end LeanCanny.Algebra.CharacteristicLowestBounds
