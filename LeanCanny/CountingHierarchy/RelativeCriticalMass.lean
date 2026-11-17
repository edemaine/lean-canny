/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCriticalPolynomial

/-! # Uniform source-derived mass bounds for relative critical equations -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue LeanCanny.Algebra
open scoped BigOperators Classical

variable {n : ℕ} {κ : Type*}

def relativeRelationMassExponent (d b : ℕ) : ℕ := (d + 1).size + b + 1

def relativeObjectiveMassExponent (n d b : ℕ) : ℕ := n.size + (d + 2).size + b + 2

theorem relativeLower_mass_le (d b : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) (i : Fin n) :
    MultivariateParameterMass.mass (relativeLower d F i) ≤ 2 ^ relativeRelationMassExponent d b := by
  rw [relativeLower, criticalLower, zero_pow (by omega : d + 1 ≠ 0)]
  apply (MultivariateParameterMass.sub_le _ _).trans
  rw [MultivariateParameterMass.C, MvMass.zero, Nat.zero_add]
  apply (MultivariateParameterMass.mul_le _ _).trans
  rw [MultivariateParameterMass.C, MvMass.X, Nat.one_mul]
  apply (MultivariateParameterMass.pderiv_le _ _).trans
  apply (Nat.mul_le_mul ((relativeSource_mainDegree F).trans hF) ((relativeSource_mass_le F).trans hM)).trans
  calc
    (d + 1) * 2 ^ b ≤ 2 ^ (d + 1).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = 2 ^ ((d + 1).size + b) := (pow_add 2 _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold relativeRelationMassExponent; omega)

theorem zeroCenterPotential_mass_le (ell : ℕ) (hell : 1 ≤ ell) :
    MultivariateParameterMass.mass
      (potentialPolynomial ell (fun _ : Fin n => (0 : MvPolynomial κ ℤ))) ≤ n := by
  rw [potentialPolynomial]
  simp only [zero_pow (by omega : ell ≠ 0), zero_pow (Nat.succ_ne_zero ell), mul_zero,
    map_zero, zero_mul, sub_zero, add_zero]
  apply (MultivariateParameterMass.sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ =>
      (MultivariateParameterMass.pow_le _ _).trans_eq (by rw [MultivariateParameterMass.X, one_pow]))
    _ = n := by simp

theorem relativeObjective_mass_le (d b : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hM : MvMass.mass F ≤ 2 ^ b) :
    MultivariateParameterMass.mass (relativeObjective d F) ≤ 2 ^ relativeObjectiveMassExponent n d b := by
  have hscalar : MvMass.mass (((d + 2 : ℕ) : MvPolynomial (Option κ) ℤ) * MvPolynomial.X none) ≤ d + 2 := by
    apply (MvMass.mul_le _ _).trans
    rw [MvMass.X, Nat.mul_one, ← MvPolynomial.C_eq_natCast, MvMass.C, Int.natAbs_natCast]
  have hprod : MultivariateParameterMass.mass
      (MvPolynomial.C (((d + 2 : ℕ) : MvPolynomial (Option κ) ℤ) * MvPolynomial.X none) * relativeSource F) ≤
      (d + 2) * 2 ^ b := by
    apply (MultivariateParameterMass.mul_le _ _).trans
    rw [MultivariateParameterMass.C]
    exact Nat.mul_le_mul hscalar ((relativeSource_mass_le F).trans hM)
  have hp : MultivariateParameterMass.mass (relativeObjective d F) ≤ n + (d + 2) * 2 ^ b := by
    exact (MultivariateParameterMass.add_le _ _).trans
      (Nat.add_le_add (zeroCenterPotential_mass_le (κ := Option κ) (d + 1) (by omega)) hprod)
  let B := n.size + (d + 2).size + b
  have hn : n ≤ 2 ^ B := (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by decide) (by dsimp only [B]; omega))
  have hm : (d + 2) * 2 ^ b ≤ 2 ^ B := by
    apply (Nat.mul_le_mul_right (2 ^ b) (Nat.lt_size_self (d + 2)).le).trans
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by dsimp only [B]; omega)
  apply hp.trans
  apply (Nat.add_le_add hn hm).trans
  have he : relativeObjectiveMassExponent n d b = B + 2 := rfl
  rw [he]
  simp only [pow_add, Nat.reducePow]
  omega

end LeanCanny.CountingHierarchy
