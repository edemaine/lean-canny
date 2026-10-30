/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveValueGramSpace

/-! # Binary coefficient-height bounds for complete value determinants

A source coefficient-mass exponent gives an explicit bit bound on every
integer coefficient of the bivariate annihilator. The exponent itself has
native binary metadata even when the full coefficient is exponentially long.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveValueGram
open MvPolynomial
open scoped Classical

def massExponent (n W b : ℕ) : ℕ :=
  (dimension n W).size * dimension n W + dimension n W * ((dimension n W).size + 2 * (b + 1))

theorem annihilator_mass_le_two_pow {n : ℕ}
    (H : Fin n → MvPolynomial (Fin (n + 1)) Base) (F : MvPolynomial (Fin (n + 1)) Base)
    (d : Fin n → ℕ) (e W b : ℕ)
    (hH : ∀ i u, coefficientMass ((H i).coeff u) ≤ 2 ^ b)
    (hF : ∀ u, coefficientMass (F.coeff u) ≤ 2 ^ b) :
    NestedMass.mass (annihilator H F d e W) ≤ 2 ^ massExponent n W b := by
  let C := FixedWidthPolynomial.count (n + 1) W
  let L := dimension n W
  have hc : C ≤ L := by
    change C ≤ (n + 3) * C
    simpa only [one_mul] using Nat.mul_le_mul_right C (by omega : 1 ≤ n + 3)
  have hf : (n + 2) * C ≤ L := Nat.mul_le_mul_right C (by omega : n + 2 ≤ n + 3)
  have hm : 2 ^ b + 1 ≤ 2 ^ (b + 1) := by
    rw [pow_succ]
    have hh : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by decide)
    omega
  have hfac : C.factorial ≤ 2 ^ (L.size * L) := by
    calc
      _ ≤ C ^ C := Nat.factorial_le_pow C
      _ ≤ (2 ^ L.size) ^ C := Nat.pow_le_pow_left (hc.trans (Nat.lt_size_self L).le) C
      _ = 2 ^ (L.size * C) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ (L.size * L) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hc)
  have hb : (n + 2) * C * (2 ^ b + 1) ^ 2 ≤ 2 ^ (L.size + 2 * (b + 1)) := by
    calc
      _ ≤ L * (2 ^ (b + 1)) ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hm 2)
      _ ≤ 2 ^ L.size * (2 ^ (b + 1)) ^ 2 := Nat.mul_le_mul_right _ (Nat.lt_size_self L).le
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hp : ((n + 2) * C * (2 ^ b + 1) ^ 2) ^ C ≤ 2 ^ (L * (L.size + 2 * (b + 1))) := by
    calc
      _ ≤ (2 ^ (L.size + 2 * (b + 1))) ^ C := Nat.pow_le_pow_left hb C
      _ = 2 ^ ((L.size + 2 * (b + 1)) * C) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ ((L.size + 2 * (b + 1)) * L) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hc)
      _ = _ := by rw [Nat.mul_comm _ L]
  have h := (annihilator_mass_le H F d e W (2 ^ b) hH hF).trans (Nat.mul_le_mul hfac hp)
  simpa only [← pow_add, massExponent, L] using h

theorem annihilator_height_le {n : ℕ}
    (H : Fin n → MvPolynomial (Fin (n + 1)) Base) (F : MvPolynomial (Fin (n + 1)) Base)
    (d : Fin n → ℕ) (e W b : ℕ)
    (hH : ∀ i u, coefficientMass ((H i).coeff u) ≤ 2 ^ b)
    (hF : ∀ u, coefficientMass (F.coeff u) ≤ 2 ^ b) (j k : ℕ) :
    ((((annihilator H F d e W).coeff j).coeff k).natAbs).size ≤ massExponent n W b + 1 := by
  have hb := (coeff_natAbs_le_coefficientMass ((annihilator H F d e W).coeff j) k).trans
    ((NestedMass.coeff_le _ j).trans (annihilator_mass_le_two_pow H F d e W b hH hF))
  simpa only [Nat.size_pow] using Nat.size_le_size hb

end LeanCanny.Algebra.ProjectiveValueGram

namespace LeanCanny.Algebra.ProjectiveValueGramBits
open LeanCanny.Encoding LeanCanny.Computation

theorem Family.massExponent_binary (F : Family) (h : F.layout.Controls) (b : List Bool → ℕ) (hb : BinaryFn b) :
    BinaryFn (fun c => ProjectiveValueGram.massExponent (F.arity c) (F.width c) (b c)) := by
  have hn := F.dimension_binary h
  exact (hn.size.mul hn).add (hn.mul (hn.size.add ((BinaryFn.const 2).mul (hb.add (BinaryFn.const 1)))))

end LeanCanny.Algebra.ProjectiveValueGramBits
