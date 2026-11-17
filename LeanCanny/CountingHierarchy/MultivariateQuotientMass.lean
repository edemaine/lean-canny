/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.MultivariateResidueMass
public import LeanCanny.CountingHierarchy.MultivariateNewtonMass
public import LeanCanny.CountingHierarchy.QuotientMassBounds
public import LeanCanny.CountingHierarchy.QuotientCharacteristicEvaluation
public import LeanCanny.Algebra.PrincipalParameterMass

/-! # Pure-power characteristic mass with multivariate parameters -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {τ : Type*}

namespace PurePowerResidue.MultivariateParameters

/-- A bound obtained from the displayed small Jacobian determinant. -/
theorem jacobian_parameterMass_le {n : ℕ} (d br : ℕ)
    (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d)
    (hM : ∀ i, MultivariateParameterMass.mass (r i) ≤ 2 ^ br) :
    MultivariateParameterMass.mass (jacobian (d + 1) r) ≤
      2 ^ (n.size * n + n * ((d + 1).size + br + 1)) := by
  have hentry (i j : Fin n) :
      MultivariateParameterMass.mass (pderiv j (MvPolynomial.X i ^ (d + 1) - r i)) ≤
        2 ^ ((d + 1).size + br + 1) := by
    have hdeg : (MvPolynomial.X i ^ (d + 1) - r i).totalDegree ≤ d + 1 := by
      apply (totalDegree_sub _ _).trans
      apply max_le _ ((hr i).trans (Nat.le_succ d))
      exact (totalDegree_pow _ _).trans (by simp only [totalDegree_X, mul_one, le_refl])
    have hm : MultivariateParameterMass.mass (MvPolynomial.X i ^ (d + 1) - r i) ≤ 1 + 2 ^ br :=
      (MultivariateParameterMass.sub_le _ _).trans
        (Nat.add_le_add ((MultivariateParameterMass.pow_le _ _).trans_eq (by rw [MultivariateParameterMass.X, one_pow])) (hM i))
    apply (MultivariateParameterMass.pderiv_le _ _).trans
    apply (Nat.mul_le_mul hdeg hm).trans
    calc
      (d + 1) * (1 + 2 ^ br) ≤ 2 ^ (d + 1).size * (2 ^ br * 2) := by
        apply Nat.mul_le_mul (Nat.lt_size_self _).le
        have := Nat.one_le_two_pow (n := br)
        omega
      _ = _ := by simp only [← pow_succ, ← pow_add, Nat.add_assoc]
  have hf : n.factorial ≤ 2 ^ (n.size * n) :=
    (Nat.factorial_le_pow _).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self n).le n).trans_eq (pow_mul _ _ _).symm)
  apply (MultivariateParameterMass.det_le _ _ hentry).trans
  simp only [Fintype.card_fin]
  exact (Nat.mul_le_mul_right _ hf).trans_eq (by rw [← pow_mul, ← pow_add]; congr 1; ring)

theorem multiplicationMatrix_trace_mass_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (B D bv br bJ : ℕ) (k : ℕ) (hk : k ≤ D)
    (hB : (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hv : MultivariateParameterMass.mass v ≤ 2 ^ bv)
    (hM : ∀ i, MultivariateParameterMass.mass (r i) ≤ 2 ^ br)
    (hJ : MultivariateParameterMass.mass (jacobian (d + 1) r) ≤ 2 ^ bJ) :
    MvMass.mass (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) ^ k).trace) ≤
        2 ^ traceMassExponent n B D bv br bJ := by
  rw [multiplicationMatrix_trace_pow d hd r hr v k]
  apply (residue_mass_le (by omega : 1 ≤ d + 1) B (2 ^ br)
    (Nat.one_le_two_pow) r (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) hM _ hB).trans
  have hm : MultivariateParameterMass.mass (v ^ k * jacobian (d + 1) r) ≤ 2 ^ (D * bv + bJ) := by
    apply (MultivariateParameterMass.mul_le _ _).trans
    apply (Nat.mul_le_mul ((MultivariateParameterMass.pow_le _ _).trans (Nat.pow_le_pow_left hv _)) hJ).trans
    rw [← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm bv k] using
      (Nat.add_le_add_right (Nat.mul_le_mul_right bv hk) bJ))
  apply (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_size_self (B + 1)).le n)
    (Nat.mul_le_mul_right _ hm)).trans_eq
  simp only [← pow_mul, ← pow_add, traceMassExponent]
  congr 1
  ring

/-- Total mass of the actual quotient characteristic polynomial, bounded
 using the residue traces rather than expanded normal-form matrix entries. -/
theorem multiplicationMatrix_charpoly_nestedMass_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (Ω bv br : ℕ) (hvdeg : v.totalDegree ≤ Ω)
    (hv : MultivariateParameterMass.mass v ≤ 2 ^ bv)
    (hM : ∀ i, MultivariateParameterMass.mass (r i) ≤ 2 ^ br) :
    PolynomialParameterMass.mass
      ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly) ≤
      2 ^ (traceMassExponent n ((d + 1) ^ n * Ω + n * d) ((d + 1) ^ n) bv br
        (n.size * n + n * ((d + 1).size + br + 1)) * (d + 1) ^ n +
          ((d + 1) ^ n + 1).size) := by
  have hJ := jacobian_parameterMass_le d br r hr hM
  have ht (j : ℕ) (_hj : 1 ≤ j) (hle : j ≤ (d + 1) ^ n) :=
    multiplicationMatrix_trace_mass_le d hd r hr v
      ((d + 1) ^ n * Ω + n * d) ((d + 1) ^ n) bv br
      (n.size * n + n * ((d + 1).size + br + 1)) j hle
      (quotient_trace_numerator_degree d r hr v Ω ((d + 1) ^ n) j hvdeg hle) hv hM hJ
  simpa only [card_normalIndex] using MultivariateNewtonMass.charpoly_nestedMass_le
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) _
    (fun j hj hle => ht j hj (by simpa only [card_normalIndex] using hle))

end PurePowerResidue.MultivariateParameters
end LeanCanny.CountingHierarchy
