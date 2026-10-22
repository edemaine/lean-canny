/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefree
public import LeanCanny.Algebra.SubresultantBounds
public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.Algebra.NestedCoefficientMass

/-! # Source bounds for symbolic squarefree preprocessing

The symbolic GCD and scaled quotient have bounds in both variables and in
total integer coefficient mass. The budgets depend only on the original
outer degree and coefficient-mass bound, and not on the selected GCD order.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicScaledSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical BigOperators
attribute [local irreducible] Matrix.det

theorem derivative_inner_degree (p : Polynomial Coefficient) (E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (k : ℕ) :
    (p.derivative.coeff k).natDegree ≤ E := by
  rw [coeff_derivative, ← Nat.cast_add_one]
  change (p.coeff (k + 1) * C ((k + 1 : ℕ) : ℤ)).natDegree ≤ E
  exact natDegree_mul_le.trans (by simpa only [natDegree_C, Nat.add_zero] using hE (k + 1))

theorem gcd_inner_degree (p : Polynomial Coefficient) (E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (k : ℕ) :
    ((gcd p).coeff k).natDegree ≤ 2 * p.natDegree * E := by
  rw [gcd]
  split_ifs with hd
  · simp only [coeff_one]
    split_ifs <;> simp
  · rw [coefficientForm_coeff]
    split_ifs
    · rw [subresultantCoeff_eq_minor_det]
      apply (Subresultant.minor_natDegree_le p p.derivative p.natDegree
        p.derivative.natDegree (degree p) k E E hE (derivative_inner_degree p E hE)).trans
      have hn := natDegree_derivative_le p
      have hs : (p.natDegree - degree p) + (p.derivative.natDegree - degree p) ≤ 2 * p.natDegree := by omega
      simpa only [← Nat.add_mul] using Nat.mul_le_mul_right E hs
    · simp

theorem polynomial_inner_degree (p : Polynomial Coefficient) (E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (k : ℕ) :
    ((polynomial p).coeff k).natDegree ≤ (p.natDegree + 1) * ((2 * p.natDegree + 1) * E) := by
  rw [polynomial, ScaledPolynomialQuotient.quotient_coeff]
  split_ifs with hk
  · let N := p.natDegree - degree p + 1
    let B := (2 * p.natDegree + 1) * E
    have hp (i : ℕ) : (p.coeff i).natDegree ≤ B :=
      (hE i).trans (by dsimp [B]; nlinarith)
    have hg (i : ℕ) : ((gcd p).coeff i).natDegree ≤ B :=
      (gcd_inner_degree p E hE i).trans (by dsimp [B]; nlinarith)
    have he (i j : Fin N) :
        (((ScaledPolynomialQuotient.matrix (gcd p) (degree p) (p.natDegree - degree p)).updateCol
          ⟨k, hk⟩ (ScaledPolynomialQuotient.input p (degree p) (p.natDegree - degree p))) i j).natDegree ≤ B := by
      rw [ScaledPolynomialQuotient.selected_entry]
      split_ifs
      · exact hp _
      · exact hg _
      · simp
    have h := det_natDegree_le _ (fun _ : Fin N => B) he
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right B (by dsimp [N]; omega))
  · simp

theorem derivative_coefficient_mass (p : Polynomial Coefficient) (b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) (k : ℕ) :
    coefficientMass (p.derivative.coeff k) ≤ 2 ^ (b + p.natDegree.size) := by
  rw [coeff_derivative, ← Nat.cast_add_one]
  by_cases hk : k + 1 ≤ p.natDegree
  · change coefficientMass (p.coeff (k + 1) * C ((k + 1 : ℕ) : ℤ)) ≤ _
    apply (coefficientMass_mul_le _ _).trans
    rw [coefficientMass_C, Int.natAbs_natCast, pow_add]
    exact Nat.mul_le_mul (hb _) (hk.trans (Nat.lt_size_self _).le)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, coefficientMass_zero]
    exact Nat.zero_le _

def gcdMassExponent (D b : ℕ) : ℕ := (2 * D).size * (2 * D) + (2 * D) * (b + D.size)

theorem gcd_coefficient_mass (p : Polynomial Coefficient) (b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) (k : ℕ) :
    coefficientMass ((gcd p).coeff k) ≤ 2 ^ gcdMassExponent p.natDegree b := by
  rw [gcd]
  split_ifs
  · simp only [coeff_one]
    split_ifs
    · have hmone : coefficientMass (1 : ℤ[X]) = 1 := by
        simpa only [Polynomial.C_1, Int.natAbs_one] using coefficientMass_C (1 : ℤ)
      simpa only [hmone] using Nat.one_le_two_pow (n := gcdMassExponent p.natDegree b)
    · simp
  · rw [coefficientForm_coeff]
    split_ifs
    · rw [subresultantCoeff_eq_minor_det]
      have hp (i : ℕ) : coefficientMass (p.coeff i) ≤ 2 ^ (b + p.natDegree.size) :=
        (hb i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
      have he (i j : Fin ((p.natDegree - degree p) + (p.derivative.natDegree - degree p))) :
          coefficientMass (Subresultant.minor p p.derivative p.natDegree p.derivative.natDegree
            (degree p) k i j) ≤ 2 ^ (b + p.natDegree.size) := by
        induction j using Fin.addCases <;>
          simp only [Subresultant.minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Subresultant.band]
        all_goals split_ifs
        all_goals first | exact hp _ | exact derivative_coefficient_mass p b hb _ | simp
      have h := det_coefficientMass_le_pow _ (b + p.natDegree.size) he
      simp only [Fintype.card_fin] at h
      apply h.trans
      apply Nat.pow_le_pow_right (by decide)
      have hn := natDegree_derivative_le p
      have hN : (p.natDegree - degree p) + (p.derivative.natDegree - degree p) ≤ 2 * p.natDegree := by omega
      exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right _ hN)
    · simp

def massExponent (D b : ℕ) : ℕ :=
  (D + 1).size * (D + 1) + (D + 1) * (gcdMassExponent D b + b)

theorem polynomial_coefficient_mass (p : Polynomial Coefficient) (b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) (k : ℕ) :
    coefficientMass ((polynomial p).coeff k) ≤ 2 ^ massExponent p.natDegree b := by
  rw [polynomial, ScaledPolynomialQuotient.quotient_coeff]
  split_ifs with hk
  · let N := p.natDegree - degree p + 1
    let B := gcdMassExponent p.natDegree b + b
    have hp (i : ℕ) : coefficientMass (p.coeff i) ≤ 2 ^ B :=
      (hb i).trans (Nat.pow_le_pow_right (by decide) (by dsimp [B]; omega))
    have hg (i : ℕ) : coefficientMass ((gcd p).coeff i) ≤ 2 ^ B :=
      (gcd_coefficient_mass p b hb i).trans (Nat.pow_le_pow_right (by decide) (by dsimp [B]; omega))
    have he (i j : Fin N) :
        coefficientMass (((ScaledPolynomialQuotient.matrix (gcd p) (degree p) (p.natDegree - degree p)).updateCol
          ⟨k, hk⟩ (ScaledPolynomialQuotient.input p (degree p) (p.natDegree - degree p))) i j) ≤ 2 ^ B := by
      rw [ScaledPolynomialQuotient.selected_entry]
      split_ifs
      · exact hp _
      · exact hg _
      · simp
    have h := det_coefficientMass_le_pow _ B he
    simp only [Fintype.card_fin] at h
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    have hN : N ≤ p.natDegree + 1 := by dsimp [N]; omega
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right B hN)
  · simp

theorem polynomial_mass (p : Polynomial Coefficient) (b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) :
    NestedMass.mass (polynomial p) ≤ 2 ^ (massExponent p.natDegree b + (p.natDegree + 1).size) :=
  NestedMass.le_pow _ _ _ (polynomial_natDegree_le p) (polynomial_coefficient_mass p b hb)

end LeanCanny.Algebra.SymbolicScaledSquarefree
