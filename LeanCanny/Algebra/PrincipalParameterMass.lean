/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Algebra.PrincipalSubresultant.Signed

/-! # Parameter-polynomial mass bounds for signed principal coefficients

The determinant's whole coefficient mass, rather than each coefficient
separately, is bounded by the Leibniz expansion. No parameter degree is needed.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial
open scoped BigOperators

theorem det_coefficientMass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ[X]) (B : ι → ℕ) (hB : ∀ i j, coefficientMass (A i j) ≤ B j) :
    coefficientMass A.det ≤ (Fintype.card ι).factorial * ∏ j, B j := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, coefficientMass (Equiv.Perm.sign σ • ∏ j, A (σ j) j) := coefficientMass_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ j, B j := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Units.smul_def, Polynomial.smul_eq_C_mul]
      calc
        _ ≤ coefficientMass (Polynomial.C (Equiv.Perm.sign σ : ℤ)) * coefficientMass (∏ j, A (σ j) j) :=
          coefficientMass_mul_le _ _
        _ = coefficientMass (∏ j, A (σ j) j) := by rw [coefficientMass_C, Int.units_natAbs, one_mul]
        _ ≤ ∏ j, coefficientMass (A (σ j) j) := coefficientMass_prod_le _ _
        _ ≤ ∏ j, B j := Finset.prod_le_prod fun j _ => hB (σ j) j
    _ = _ := by simp [Fintype.card_perm]

theorem det_coefficientMass_le_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ[X]) (b : ℕ) (hb : ∀ i j, coefficientMass (A i j) ≤ 2 ^ b) :
    coefficientMass A.det ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι + Fintype.card ι * b) := by
  have hf : (Fintype.card ι).factorial ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι) :=
    (Nat.factorial_le_pow _).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self _).le _).trans_eq (pow_mul _ _ _).symm)
  calc
    _ ≤ (Fintype.card ι).factorial * ∏ _j : ι, 2 ^ b := det_coefficientMass_le A (fun _ => 2 ^ b) hb
    _ ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι) * ∏ _j : ι, 2 ^ b := Nat.mul_le_mul_right _ hf
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul, ← pow_add, Nat.mul_comm b]

namespace PrincipalSubresultant

def parameterMassBound (R a : ℕ) : ℕ := R.size * R + R * a + a

theorem signedPsc_mass_le (p q : (ℤ[X])[X]) (m n j R a : ℕ) (hR : m + n ≤ R)
    (hp : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ a)
    (hq : ∀ i, coefficientMass (q.coeff i) ≤ 2 ^ a) :
    coefficientMass (signedPsc p q m n j) ≤ 2 ^ parameterMassBound R a := by
  have ha : a ≤ parameterMassBound R a := by unfold parameterMassBound; omega
  have hpow : 2 ^ a ≤ 2 ^ parameterMassBound R a := Nat.pow_le_pow_right (by decide) ha
  by_cases hj : j ≤ min m n
  · rw [signedPsc_of_le p q hj]
    have hs : coefficientMass ((-1 : ℤ[X]) ^ (m - j).choose 2) ≤ 1 := by
      have h := coefficientMass_pow_le (-1 : ℤ[X]) ((m - j).choose 2)
      simpa only [← Polynomial.C_neg, ← Polynomial.C_1, coefficientMass_C, Int.natAbs_neg,
        show (1 : ℤ).natAbs = 1 from rfl, one_pow] using h
    have hcol : ∀ i k, coefficientMass (subresultantMatrix p q m n j i k) ≤ 2 ^ a := by
      intro i k
      induction k using Fin.addCases <;> simp only [subresultantMatrix_castAdd, subresultantMatrix_natAdd]
      · split_ifs
        · exact hq _
        · simp
      · split_ifs
        · exact hp _
        · simp
    have hd := det_coefficientMass_le_pow (subresultantMatrix p q m n j) a hcol
    have hN : (m - j) + (n - j) ≤ R := by omega
    have he : ((m - j) + (n - j)).size * ((m - j) + (n - j)) + ((m - j) + (n - j)) * a ≤ parameterMassBound R a := by
      have h1 := Nat.mul_le_mul (Nat.size_le_size hN) hN
      have h2 := Nat.mul_le_mul_right a hN
      unfold parameterMassBound
      omega
    calc
      _ ≤ coefficientMass ((-1 : ℤ[X]) ^ (m - j).choose 2) * coefficientMass (psc p q m n j) := coefficientMass_mul_le _ _
      _ ≤ 1 * coefficientMass (psc p q m n j) := Nat.mul_le_mul_right _ hs
      _ = coefficientMass (subresultantMatrix p q m n j).det := by rw [one_mul, psc_def]
      _ ≤ 2 ^ (((m - j) + (n - j)).size * ((m - j) + (n - j)) + ((m - j) + (n - j)) * a) := by
        simpa only [Fintype.card_fin] using hd
      _ ≤ _ := Nat.pow_le_pow_right (by decide) he
  · rw [signedPsc_of_lt p q (by omega)]
    split_ifs
    · exact (hp _).trans hpow
    · exact (hq _).trans hpow
    · simp

end PrincipalSubresultant
end LeanCanny.Algebra
