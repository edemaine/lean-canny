/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateMap

/-! # Literal relative annihilators commute with coefficient maps

The fixed reduction choices and padded index set do not depend on the
coefficient ring. Their matrix powers, relative characteristic polynomial
and integer rescaling consequently commute with arbitrary coefficient
maps, including noninjective nilpotent substitutions.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerAnnihilatorMap
open MvPolynomial
open scoped Classical
variable {R A : Type*} [CommRing R] [CommRing A] {n B : ℕ}

theorem reduction (φ : R →+* A) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (bound : ℕ) :
    (PurePowerReductionMatrix.matrix (B := B) fallback d low c bound).map φ =
      PurePowerReductionMatrix.matrix (B := B) fallback d (fun i => (low i).map φ) (φ c) bound := by
  ext i j
  simp only [Matrix.map_apply, PurePowerReductionMatrix.matrix]
  split_ifs
  · rfl
  · exact map_zero φ
  · rw [← MvPolynomial.coeff_map]
    simp only [MonicMonomialReduction.step, map_neg, map_mul, MvPolynomial.map_monomial, map_one]
  · exact map_zero φ

theorem padded {σ : Type*} [Fintype σ] [DecidableEq σ] (φ : R →+* A)
    (T : Matrix σ σ R) (normal : σ → Prop) (bound : ℕ) (shift : σ → σ) :
    (GradedReductionAnnihilator.paddedMatrix T normal bound shift).map φ =
      GradedReductionAnnihilator.paddedMatrix (T.map φ) normal bound shift := by
  ext i j
  simp only [Matrix.map_apply, GradedReductionAnnihilator.paddedMatrix]
  split_ifs
  · exact congrArg (fun M => M i (shift j)) (Matrix.map_pow T φ (bound + 1))
  · exact map_zero φ

theorem action (φ : R →+* A) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (bound : ℕ)
    (hgrid : PurePowerReductionMatrix.gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (j : Fin n) :
    (PurePowerRelativeAnnihilator.actionMatrix fallback d low c bound hgrid hbound j).map φ =
      PurePowerRelativeAnnihilator.actionMatrix fallback d (fun i => (low i).map φ) (φ c) bound hgrid hbound j := by
  unfold PurePowerRelativeAnnihilator.actionMatrix
  rw [padded, reduction]

theorem polynomial (φ : R →+* A) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (bound : ℕ)
    (hgrid : PurePowerReductionMatrix.gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (j : Fin n) :
    (PurePowerRelativeAnnihilator.polynomial fallback d low c bound hgrid hbound j).map φ =
      PurePowerRelativeAnnihilator.polynomial fallback d (fun i => (low i).map φ) (φ c) bound hgrid hbound j := by
  unfold PurePowerRelativeAnnihilator.polynomial
  rw [← action φ fallback d low c bound hgrid hbound j]
  simp only [ScaledGradedReductionAnnihilator.polynomial, Polynomial.map_comp, Matrix.charpoly_map,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, map_pow, Polynomial.map_X]

theorem cleared {k : ℕ} (φ : R →+* A) (D : ℕ) (q : R) (H : ℕ → R)
    (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (r j : Fin (k + 1)) :
    (ClearedCoordinateCritical.annihilator D q H offset hfit low a r j).map φ =
      ClearedCoordinateCritical.annihilator D (φ q) (fun i => φ (H i)) offset hfit (low.map φ) (φ a) r j := by
  unfold ClearedCoordinateCritical.annihilator
  rw [polynomial]
  simp only [map_mul, map_pow, map_natCast, ClearedCoordinateMap.lower]

end LeanCanny.Algebra.PurePowerAnnihilatorMap
