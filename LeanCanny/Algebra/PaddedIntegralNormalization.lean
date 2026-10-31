/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedDegreeIntegralNormalization
public import Mathlib.RingTheory.AdjoinRoot

/-! # Monic scalar equations of one uniform degree

Padding a selected normalization by a power of X preserves its roots and
gives every branch the same positive degree. Invalid advertised degrees use
the pure power. This fixes the rank of each integral parameter extension.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralNormalization
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]

noncomputable def polynomial (p : Polynomial R) (d N : ℕ) : Polynomial R :=
  if d ≤ N then X ^ (N - d) * FixedDegreeIntegralNormalization.polynomial p d else X ^ N

theorem coefficient (p : Polynomial R) (d N k : ℕ) :
    (polynomial p d N).coeff k =
      if d ≤ N then
        if N - d ≤ k then (FixedDegreeIntegralNormalization.polynomial p d).coeff (k - (N - d)) else 0
      else if k = N then 1 else 0 := by
  by_cases hd : d ≤ N
  · simp only [polynomial, ite_eq_left hd]
    exact coeff_X_pow_mul' (FixedDegreeIntegralNormalization.polynomial p d) (N - d) k
  · simp only [polynomial, ite_eq_right hd, coeff_X_pow]

theorem coefficient_below (p : Polynomial R) (d N : ℕ) (i : Fin N) :
    (polynomial p d N).coeff i.val =
      if d ≤ N ∧ N - d ≤ i.val then
        p.coeff (i.val - (N - d)) * p.coeff d ^ (d - 1 - (i.val - (N - d))) else 0 := by
  rw [coefficient]
  by_cases hd : d ≤ N
  · rw [ite_eq_left hd]
    by_cases hi : N - d ≤ i.val
    · have HK : i.val - (N - d) < d := by have := i.isLt; omega
      rw [ite_eq_left hi, ite_eq_left ⟨hd, hi⟩, FixedDegreeIntegralNormalization.coefficient,
        ite_eq_right (by omega), ite_eq_left HK, zero_add]
    · rw [ite_eq_right hi, ite_eq_right (by tauto)]
  · rw [ite_eq_right hd, ite_eq_right (by have := i.isLt; omega), ite_eq_right (by tauto)]

theorem monic [Nontrivial R] (p : Polynomial R) (d N : ℕ) : (polynomial p d N).Monic := by
  unfold polynomial
  split_ifs
  · exact (monic_X_pow _).mul (FixedDegreeIntegralNormalization.monic p d)
  · exact monic_X_pow _

theorem natDegree [Nontrivial R] (p : Polynomial R) (d N : ℕ) : (polynomial p d N).natDegree = N := by
  unfold polynomial
  split_ifs with hd
  · rw [(monic_X_pow _).natDegree_mul (FixedDegreeIntegralNormalization.monic p d), natDegree_X_pow,
      FixedDegreeIntegralNormalization.natDegree, Nat.sub_add_cancel hd]
  · exact natDegree_X_pow _

theorem scaled_root {K : Type*} [Field K] (p : Polynomial R) (d N : ℕ) (hdN : d ≤ N) (φ : R →+* K)
    (hd : (p.map φ).natDegree = d) (hpos : 1 ≤ d) (x : K) (hx : p.eval₂ φ x = 0) :
    (polynomial p d N).eval₂ φ (φ (p.coeff d) * x) = 0 := by
  rw [polynomial, ite_eq_left hdN, eval₂_mul, FixedDegreeIntegralNormalization.scaled_root p d φ hd hpos x hx, mul_zero]

theorem extension_nontrivial [Nontrivial R] (p : Polynomial R) (d N : ℕ) (hN : 0 < N) :
    Nontrivial (AdjoinRoot (polynomial p d N)) := by
  apply (AdjoinRoot.nontrivial_iff_of_monic (monic p d N)).mpr
  rw [Polynomial.degree_eq_natDegree (monic p d N).ne_zero, natDegree]
  exact_mod_cast hN

end LeanCanny.Algebra.PaddedIntegralNormalization
