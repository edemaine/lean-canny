/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass

/-! # Linear heights with explicit polynomial bounds

A height can use any selected ambient block. Its evaluation is the actual
linear functional, its degree is at most one, and its coefficient mass is
bounded by the sum of the direction coefficients. Variables need not be
injectively selected for these bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineHeightPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {n : ℕ} {ι R : Type*} [CommRing R]

noncomputable def polynomial (a : Fin n → R) (f : Fin n → ι) : MvPolynomial ι R :=
  ∑ i, C (a i) * X (f i)

def value (a x : Fin n → R) : R := ∑ i, a i * x i

theorem eval {K : Type*} [CommRing K] (φ : R →+* K) (a : Fin n → R) (f : Fin n → ι) (z : ι → K) :
    (polynomial a f).eval₂ φ z = ∑ i, φ (a i) * z (f i) := by
  simp [polynomial]

theorem degree_le [Nontrivial R] (a : Fin n → R) (f : Fin n → ι) :
    (polynomial a f).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

omit [CommRing R] in
theorem mass_le (a : Fin n → ℤ) (f : Fin n → ι) (U : ℕ) (ha : ∀ i, (a i).natAbs ≤ U) :
    MvMass.mass (polynomial a f) ≤ n * U := by
  apply (MvMass.sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, U := Finset.sum_le_sum (fun i _ => by
      exact (MvMass.mul_le _ _).trans (by simpa only [MvMass.C, MvMass.X, Nat.mul_one] using ha i))
    _ = n * U := by simp

noncomputable def midpointLevel (a : Fin n → R) (left right : Fin n → ι) : MvPolynomial ι R :=
  polynomial a left + polynomial a right

theorem midpoint_eval {K : Type*} [CommRing K] (φ : R →+* K) (a : Fin n → R)
    (left right : Fin n → ι) (z : ι → K) :
    (midpointLevel a left right).eval₂ φ z =
      (∑ i, φ (a i) * z (left i)) + ∑ i, φ (a i) * z (right i) := by
  simp only [midpointLevel, eval₂_add, eval]

theorem midpoint_equation {K : Type*} [CommRing K] (φ : R →+* K) (a : Fin n → R)
    (left right current : Fin n → ι) (z : ι → K) :
    (polynomial (fun i => 2 * a i) current - midpointLevel a left right).eval₂ φ z = 0 ↔
      2 * (∑ i, φ (a i) * z (current i)) =
        (∑ i, φ (a i) * z (left i)) + ∑ i, φ (a i) * z (right i) := by
  simp only [eval₂_sub, eval, midpoint_eval, map_mul, map_ofNat, sub_eq_zero,
    mul_assoc, ← Finset.mul_sum]

theorem midpoint_degree [Nontrivial R] (a : Fin n → R) (left right : Fin n → ι) :
    (midpointLevel a left right).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (degree_le _ _) (degree_le _ _))

omit [CommRing R] in
theorem midpoint_mass (a : Fin n → ℤ) (left right : Fin n → ι) (U : ℕ) (ha : ∀ i, (a i).natAbs ≤ U) :
    MvMass.mass (midpointLevel a left right) ≤ 2 * n * U := by
  apply (MvMass.add_le _ _).trans
  calc
    _ ≤ n * U + n * U := Nat.add_le_add (mass_le a left U ha) (mass_le a right U ha)
    _ = 2 * n * U := by ring

end LeanCanny.Algebra.AffineHeightPolynomial
