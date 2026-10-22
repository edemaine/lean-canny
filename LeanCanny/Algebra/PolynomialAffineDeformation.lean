/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialKronecker
public import LeanCanny.Algebra.LinearCoefficientBounds

/-! # Encoding one affine deformation entry

An original polynomial entry is deformed toward a scalar. Its two outer
coefficients are the original entry and scalar minus entry. Radix decoding
therefore needs one original coefficient and the scalar's degree-zero test.
Encoding the deformation increases the coefficient-mass budget by at most two.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialAffineDeformation
variable {R : Type*} [CommRing R]

noncomputable def affine (a : Polynomial R) (q : R) : Polynomial (Polynomial R) :=
  Polynomial.C a + Polynomial.X * (Polynomial.C (Polynomial.C q) - Polynomial.C a)

theorem coefficient (a : Polynomial R) (q : R) (j : ℕ) :
    (affine a q).coeff j = if j = 0 then a else if j = 1 then Polynomial.C q - a else 0 := by
  rw [affine, ← map_sub Polynomial.C]
  cases j with
  | zero => simp
  | succ j =>
    cases j with
    | zero => simp
    | succ j => simp [Polynomial.coeff_X_mul]

theorem inner_degree_le (a : Polynomial R) (q : R) (E : ℕ) (ha : a.natDegree ≤ E) (j : ℕ) :
    ((affine a q).coeff j).natDegree ≤ E := by
  rw [coefficient]
  split_ifs
  · exact ha
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ha)
  · simp

theorem encoded_coefficient (a : Polynomial R) (q : R) (B d : ℕ) (hB : 0 < B) (ha : a.natDegree < B) :
    (PolynomialKronecker.encode B (affine a q)).coeff d =
      if d / B = 0 then a.coeff (d % B) else
        if d / B = 1 then (if d % B = 0 then q else 0) - a.coeff (d % B) else 0 := by
  rw [PolynomialKronecker.coefficient_any B hB _ (fun j => (inner_degree_le a q _ le_rfl j).trans_lt ha), coefficient]
  by_cases h0 : d / B = 0
  · simp only [h0, ite_true]
  · by_cases h1 : d / B = 1
    · simp only [h1, Nat.one_ne_zero, ite_false, ite_true, Polynomial.coeff_sub, Polynomial.coeff_C]
    · simp only [h0, h1, ite_false, Polynomial.coeff_zero]

theorem encoded_mass_le (a : Polynomial ℤ) (q : ℤ) (B b : ℕ)
    (ha : coefficientMass a ≤ 2 ^ b) (hq : q.natAbs ≤ 1) :
    coefficientMass (PolynomialKronecker.encode B (affine a q)) ≤ 2 ^ (b + 2) := by
  simp only [affine, map_add, map_mul, map_sub, PolynomialKronecker.encode_C, PolynomialKronecker.encode_X]
  have hm := coefficientMass_mul_le ((Polynomial.X : Polynomial ℤ) ^ B) (Polynomial.C q - a)
  rw [coefficientMass_X_pow, one_mul] at hm
  have hs := hm.trans (coefficientMass_sub_le (Polynomial.C q) a)
  rw [coefficientMass_C] at hs
  have hadd := coefficientMass_add_le a ((Polynomial.X : Polynomial ℤ) ^ B * (Polynomial.C q - a))
  have hpos := Nat.one_le_two_pow (n := b)
  rw [pow_add]
  simp only [show (2 : ℕ) ^ 2 = 4 by decide]
  omega

end LeanCanny.Algebra.PolynomialAffineDeformation
