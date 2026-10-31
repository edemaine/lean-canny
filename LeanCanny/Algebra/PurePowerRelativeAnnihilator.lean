/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionShifts
public import LeanCanny.Algebra.ScaledGradedReductionAnnihilator

/-! # Constructed relative coordinate annihilators for pure-power systems

Each equation has the same leading coefficient c and one pure-power leading
monomial. A concrete fixed-width reduction matrix constructs an annihilator
for every coordinate of every specialized root. No quotient basis, reduction
table, or independence certificate is an input.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerRelativeAnnihilator
open PurePowerReductionMatrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n B : ℕ} {R : Type*} [CommRing R]

noncomputable def actionMatrix (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (bound : ℕ)
    (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) :
    Matrix (Index n B) (Index n B) R :=
  GradedReductionAnnihilator.paddedMatrix (matrix fallback d low c bound)
    (fun j => Normal d (FixedWidthPolynomial.vector n B j)) bound (shift d bound hgrid hbound r)

noncomputable def polynomial (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (bound : ℕ)
    (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) : Polynomial R :=
  ScaledGradedReductionAnnihilator.polynomial (actionMatrix fallback d low c bound hgrid hbound r) c (bound + 1)

theorem root {K : Type*} [Field K] (φ : R →+* K) (fallback : Fin n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (low : Fin n → MvPolynomial (Fin n) R) (hlow : ∀ i, (low i).totalDegree < d i)
    (c : R) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n)
    (x : Fin n → K) (hx : ∀ i, (MvPolynomial.C c * MvPolynomial.X i ^ d i + low i).eval₂ φ x = 0) :
    (polynomial fallback d low c bound hgrid hbound r).eval₂ φ (x r) = 0 := by
  unfold polynomial actionMatrix
  apply ScaledGradedReductionAnnihilator.root
  apply ScaledGradedReductionAnnihilator.padded_charpoly_root
    (matrix fallback d low c bound) (fun j => Normal d (FixedWidthPolynomial.vector n B j)) (degree bound) c
    (normal_column fallback d low c bound) (decreases fallback d low hlow c bound) bound (degree_le bound)
    (shift d bound hgrid hbound r) φ (evaluation φ bound x)
    (evaluation_relation φ fallback d low hlow c bound hbound x hx) (x r)
    (evaluation_shift φ d bound hgrid hbound r x) ?_
  refine ⟨zeroIndex n B, zero_normal d hd, ?_⟩
  rw [evaluation_zero]
  exact one_ne_zero

theorem specialized_degree {K : Type*} [Field K] (φ : R →+* K) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (hc : φ c ≠ 0) (bound : ℕ)
    (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) :
    ((polynomial fallback d low c bound hgrid hbound r).map φ).natDegree = FixedWidthPolynomial.count n B := by
  simpa only [polynomial, Fintype.card_fin] using
    ScaledGradedReductionAnnihilator.specialized_degree
      (actionMatrix fallback d low c bound hgrid hbound r) c (bound + 1) φ hc

theorem specialized_ne_zero {K : Type*} [Field K] (φ : R →+* K) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (hc : φ c ≠ 0) (bound : ℕ)
    (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) :
    (polynomial fallback d low c bound hgrid hbound r).map φ ≠ 0 := by
  have H := specialized_degree φ fallback d low c hc bound hgrid hbound r
  intro Hz
  rw [Hz, Polynomial.natDegree_zero] at H
  have HP : 0 < FixedWidthPolynomial.count n B := pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) B) n
  omega

end LeanCanny.Algebra.PurePowerRelativeAnnihilator
