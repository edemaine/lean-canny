/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.NestedMassSwap
public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.CountingHierarchy.IntegerAlgebraicThreshold

/-! # Integer coefficient bounds under bivariate specialization -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

/-- Specializing an integer polynomial multiplies its mass bound by at
 most the absolute argument raised to an advertised degree bound. -/
theorem natAbs_eval_le_mass (p : Polynomial ℤ) (D : ℕ) (hD : p.natDegree ≤ D)
    (R : ℤ) (hR : 1 ≤ R.natAbs) :
    (p.eval R).natAbs ≤ coefficientMass p * R.natAbs ^ D := by
  rw [Polynomial.eval_eq_sum_range]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs * R.natAbs ^ D := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Int.natAbs_mul, Int.natAbs_pow]
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right hR (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by
      rw [← Finset.sum_mul, coefficientMass,
        p.sum_over_range' (fun _ => rfl) (p.natDegree + 1) (Nat.lt_succ_self _)]

/-- The total mass bound is retained when specializing one variable. -/
theorem coefficientMass_map_eval_le (P : Polynomial (Polynomial ℤ)) (D : ℕ)
    (hD : ∀ i, (P.coeff i).natDegree ≤ D) (R : ℤ) (hR : 1 ≤ R.natAbs) :
    coefficientMass (P.map (Polynomial.evalRingHom R)) ≤ NestedMass.mass P * R.natAbs ^ D := by
  have hdeg : (P.map (Polynomial.evalRingHom R)).natDegree < P.natDegree + 1 :=
    (Polynomial.natDegree_map_le).trans_lt (Nat.lt_succ_self _)
  rw [coefficientMass, (P.map (Polynomial.evalRingHom R)).sum_over_range'
    (fun _ => rfl) (P.natDegree + 1) hdeg]
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  calc
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), coefficientMass (P.coeff i) * R.natAbs ^ D :=
      Finset.sum_le_sum (fun i _ => natAbs_eval_le_mass (P.coeff i) D (hD i) R hR)
    _ = _ := by
      rw [← Finset.sum_mul, ← NestedMass.range_sum P (P.natDegree + 1) (Nat.lt_succ_self _)]

/-- A value section has mass at most the source bivariate mass times
 `|R|^D`, where `D` bounds the original value-variable degree. -/
theorem integerValueSection_mass_le (Q : Polynomial (Polynomial ℤ)) (D : ℕ)
    (hD : Q.natDegree ≤ D) (R : ℤ) (hR : 1 ≤ R.natAbs) :
    coefficientMass (integerValueSection (Bivariate.swap Q) R) ≤
      NestedMass.mass Q * R.natAbs ^ D := by
  have hs (i : ℕ) : ((Bivariate.swap Q).coeff i).natDegree ≤ D :=
    (PolynomialKronecker.inner_degree_iff_swap (Bivariate.swap Q) D).mpr
      (by simpa only [Bivariate.swap_swap_apply] using hD) i
  simpa only [integerValueSection, NestedMass.swap] using
    coefficientMass_map_eval_le (Bivariate.swap Q) D hs R hR

/-- A short determinant budget for the derivative resultant. -/
@[expose] def derivativeResultantMassExponent (D H : ℕ) : ℕ :=
  (2 * D).size * (2 * D) + (2 * D) * (H + D.size)

theorem derivative_resultant_mass_le (Q : Polynomial (Polynomial ℤ)) (D H : ℕ)
    (hD : Q.natDegree ≤ D) (hH : NestedMass.mass Q ≤ 2 ^ H) :
    coefficientMass (Q.resultant Q.derivative) ≤ 2 ^ derivativeResultantMassExponent D H := by
  have hp (i : ℕ) : coefficientMass (Q.coeff i) ≤ 2 ^ (H + D.size) :=
    ((NestedMass.coeff_le Q i).trans hH).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hq (i : ℕ) : coefficientMass (Q.derivative.coeff i) ≤ 2 ^ (H + D.size) := by
    apply (NestedMass.coeff_le Q.derivative i).trans
    apply (NestedMass.derivative_le Q).trans
    apply (Nat.mul_le_mul hD hH).trans
    apply (Nat.mul_le_mul_right _ (Nat.lt_size_self D).le).trans_eq
    rw [← pow_add, Nat.add_comm]
  have he (i j : Fin (Q.natDegree + Q.derivative.natDegree)) :
      coefficientMass (Polynomial.sylvester Q Q.derivative Q.natDegree Q.derivative.natDegree i j) ≤
        2 ^ (H + D.size) := by
    induction j using Fin.addCases <;> simp only [Polynomial.sylvester, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · exact hq _
      · simp
    · split_ifs
      · exact hp _
      · simp
  have hN : Q.natDegree + Q.derivative.natDegree ≤ 2 * D := by
    have := Polynomial.natDegree_derivative_le Q
    omega
  apply (det_coefficientMass_le_pow _ _ he).trans
  simp only [Fintype.card_fin]
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right _ hN)

end LeanCanny.CountingHierarchy
