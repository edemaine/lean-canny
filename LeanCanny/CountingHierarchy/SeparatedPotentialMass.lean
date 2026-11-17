/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalPolynomial
public import LeanCanny.CountingHierarchy.ParameterMass

/-! # Explicit log-mass budgets for the coercive deformation -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

private theorem pow_two_sum_le (a b : ℕ) : 2 ^ a + 2 ^ b ≤ 2 ^ (a + b + 1) := by
  have ha : 2 ^ a ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : 2 ^ b ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

namespace ParameterMass

theorem add_exponent {ι : Type*} (p q : MvPolynomial ι (Polynomial ℤ)) (a b : ℕ)
    (hp : mass p ≤ 2 ^ a) (hq : mass q ≤ 2 ^ b) : mass (p + q) ≤ 2 ^ (a + b + 1) :=
  (add_le p q).trans ((Nat.add_le_add hp hq).trans (pow_two_sum_le a b))

theorem sub_exponent {ι : Type*} (p q : MvPolynomial ι (Polynomial ℤ)) (a b : ℕ)
    (hp : mass p ≤ 2 ^ a) (hq : mass q ≤ 2 ^ b) : mass (p - q) ≤ 2 ^ (a + b + 1) :=
  (sub_le p q).trans ((Nat.add_le_add hp hq).trans (pow_two_sum_le a b))

end ParameterMass

/-- A log-mass allowance for the sum of separated power potentials. -/
@[expose] def potentialMassExponent (n ell a : ℕ) : ℕ :=
  n.size + ((ell + 1).size + ell * a + 1 + ((ell + 1).size + (ell + 1) * a) + 1)

theorem potentialPolynomial_parameterMass_le {n : ℕ} (ell a : ℕ)
    (centers : Fin n → Polynomial ℤ) (hcenters : ∀ i, coefficientMass (centers i) ≤ 2 ^ a) :
    ParameterMass.mass (potentialPolynomial ell centers) ≤ 2 ^ potentialMassExponent n ell a := by
  have hc (i : Fin n) (k : ℕ) :
      coefficientMass (((ell + 1 : ℕ) : Polynomial ℤ) * centers i ^ k) ≤
        2 ^ ((ell + 1).size + k * a) := by
    apply (coefficientMass_mul_le _ _).trans
    have hnat : coefficientMass ((ell + 1 : ℕ) : Polynomial ℤ) ≤ 2 ^ (ell + 1).size := by
      rw [← Polynomial.C_eq_natCast, coefficientMass_C, Int.natAbs_natCast]
      exact (Nat.lt_size_self _).le
    exact (Nat.mul_le_mul hnat
      ((coefficientMass_pow_le _ _).trans (Nat.pow_le_pow_left (hcenters i) k))).trans_eq
        (by rw [← pow_mul, ← pow_add]; congr 1; ring)
  have hterm (i : Fin n) : ParameterMass.mass
      (MvPolynomial.X i ^ (ell + 1) - MvPolynomial.C ((ell + 1 : ℕ) * centers i ^ ell) * MvPolynomial.X i +
        MvPolynomial.C ((ell + 1 : ℕ) * centers i ^ (ell + 1))) ≤
      2 ^ ((ell + 1).size + ell * a + 1 + ((ell + 1).size + (ell + 1) * a) + 1) := by
    have hx : ParameterMass.mass (MvPolynomial.X i ^ (ell + 1) : MvPolynomial (Fin n) (Polynomial ℤ)) ≤ 2 ^ 0 := by
      simpa only [ParameterMass.X, one_pow, pow_zero] using ParameterMass.pow_le
        (MvPolynomial.X i : MvPolynomial (Fin n) (Polynomial ℤ)) (ell + 1)
    have hl : ParameterMass.mass
        (MvPolynomial.C ((ell + 1 : ℕ) * centers i ^ ell) * MvPolynomial.X i) ≤
          2 ^ ((ell + 1).size + ell * a) := by
      apply (ParameterMass.mul_le _ _).trans
      simpa only [ParameterMass.C, ParameterMass.X, Nat.mul_one] using hc i ell
    simpa only [Nat.zero_add] using ParameterMass.add_exponent _ _ _ _
      (ParameterMass.sub_exponent _ _ 0 _ hx hl)
      (show ParameterMass.mass (MvPolynomial.C ((ell + 1 : ℕ) * centers i ^ (ell + 1)) :
        MvPolynomial (Fin n) (Polynomial ℤ)) ≤ _ from by rw [ParameterMass.C]; exact hc i (ell + 1))
  apply (ParameterMass.sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ => hterm i)).trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  exact (Nat.mul_le_mul_right _ (Nat.lt_size_self n).le).trans_eq (pow_add 2 _ _).symm

/-- Each explicit center has a short coefficient-mass exponent. -/
theorem parameterCenters_mass_le {n : ℕ} (d : ℕ) (i : Fin n) :
    coefficientMass (parameterCenters d i) ≤ 2 ^ (n * (4 * (d + 1)).size) := by
  rw [parameterCenters, coefficientMass_C, Int.natAbs_natCast]
  apply (Nat.pow_le_pow_right (by omega : 1 ≤ 4 * (d + 1)) (show i.val + 1 ≤ n by have := i.isLt; omega)).trans
  exact (Nat.pow_le_pow_left (Nat.lt_size_self (4 * (d + 1))).le n).trans_eq (by
    rw [← pow_mul, Nat.mul_comm])

/-- The uniform allowance for the lower critical relations. -/
@[expose] def criticalLowerMassExponent (n d b : ℕ) : ℕ :=
  (d + 1) * (n * (4 * (d + 1)).size) + ((d + 1).size + b) + 1

/-- The uniform allowance for the deformed objective. -/
@[expose] def criticalObjectiveMassExponent (n d b : ℕ) : ℕ :=
  potentialMassExponent n (d + 1) (n * (4 * (d + 1)).size) + ((d + 2).size + b) + 1

theorem parameterLower_mass_le {n : ℕ} (d b : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) (i : Fin n) :
    ParameterMass.mass (parameterLower d F i) ≤ 2 ^ criticalLowerMassExponent n d b := by
  have hcenter : ParameterMass.mass (MvPolynomial.C (parameterCenters d i ^ (d + 1)) :
      MvPolynomial (Fin n) (Polynomial ℤ)) ≤ 2 ^ ((d + 1) * (n * (4 * (d + 1)).size)) := by
    rw [ParameterMass.C]
    exact ((coefficientMass_pow_le _ _).trans (Nat.pow_le_pow_left (parameterCenters_mass_le d i) _)).trans_eq
      (by rw [← pow_mul, Nat.mul_comm])
  have hder : ParameterMass.mass (pderiv i (F.map Polynomial.C)) ≤ 2 ^ ((d + 1).size + b) := by
    apply (ParameterMass.pderiv_le _ _).trans
    have hdeg := (PurePowerResidue.map_degree_le Polynomial.C F).trans hF
    exact (Nat.mul_le_mul hdeg (by simpa only [ParameterMass.map_C] using hM)).trans
      ((Nat.mul_le_mul_right _ (Nat.lt_size_self (d + 1)).le).trans_eq (pow_add 2 _ _).symm)
  have hX : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) = 1
    rw [coefficientMass_monomial]
    rfl
  have hp : ParameterMass.mass
      (MvPolynomial.C Polynomial.X * pderiv i (F.map Polynomial.C)) ≤ 2 ^ ((d + 1).size + b) :=
    (ParameterMass.mul_le _ _).trans (by simpa only [ParameterMass.C, hX, Nat.one_mul] using hder)
  exact ParameterMass.sub_exponent _ _ _ _ hcenter hp

theorem parameterObjective_mass_le {n : ℕ} (d b : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hM : MvMass.mass F ≤ 2 ^ b) :
    ParameterMass.mass (parameterObjective d F) ≤ 2 ^ criticalObjectiveMassExponent n d b := by
  have hpot := potentialPolynomial_parameterMass_le (n := n) (d + 1)
    (n * (4 * (d + 1)).size) (parameterCenters d) (parameterCenters_mass_le d)
  have hX : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) = 1
    rw [coefficientMass_monomial]
    rfl
  have hcoef : coefficientMass (((d + 2 : ℕ) : Polynomial ℤ) * Polynomial.X) ≤ 2 ^ (d + 2).size := by
    apply (coefficientMass_mul_le _ _).trans
    rw [hX, Nat.mul_one, ← Polynomial.C_eq_natCast, coefficientMass_C, Int.natAbs_natCast]
    exact (Nat.lt_size_self _).le
  have hterm : ParameterMass.mass
      (MvPolynomial.C (((d + 2 : ℕ) : Polynomial ℤ) * Polynomial.X) * F.map Polynomial.C) ≤
        2 ^ ((d + 2).size + b) := by
    apply (ParameterMass.mul_le _ _).trans
    rw [ParameterMass.C, ParameterMass.map_C]
    exact (Nat.mul_le_mul hcoef hM).trans_eq (pow_add 2 _ _).symm
  exact ParameterMass.add_exponent _ _ _ _ hpot hterm

end LeanCanny.CountingHierarchy
