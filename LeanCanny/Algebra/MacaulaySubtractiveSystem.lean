/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayActiveCharacteristic
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Characteristic matrices of the shifted homogeneous system

Replacing each input polynomial by `fᵢ-X*xᵢ^dᵢ` subtracts X on the
diagonal of every active principal matrix. Thus both true characteristic
determinants are determinants for the same shifted polynomial system.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) :
    Fin n → MvPolynomial (Fin n) (Polynomial R) :=
  fun i => (p i).map Polynomial.C - MvPolynomial.monomial (Finsupp.single i (d i)) Polynomial.X

theorem rowPolynomial_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r : Index n W) (hr : (FixedWidthPolynomial.vector n W r).degree = level d) :
    rowPolynomial (subtractiveSystem p d) d W r hr =
      (rowPolynomial p d W r hr).map Polynomial.C -
        MvPolynomial.monomial (FixedWidthPolynomial.vector n W r) Polynomial.X := by
  simp only [rowPolynomial, subtractiveSystem, mul_sub, map_mul, MvPolynomial.map_monomial,
    map_one, MvPolynomial.monomial_mul_monomial, one_mul, remainder_add]

theorem principal_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (s : Finset (Index n W)) (hs : s ⊆ activeIndices d W) :
    (matrix (subtractiveSystem p d) d W).submatrix (fun i : s => i.val) (fun i : s => i.val) =
      AffineCharacteristic.subtractiveMatrix ((matrix p d W).submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  funext r t
  have hr := (mem_activeIndices d W r.val).mp (hs r.property)
  change matrix (subtractiveSystem p d) d W r.val t.val =
    Polynomial.C (matrix p d W r.val t.val) - Polynomial.X * Polynomial.C ((1 : Matrix s s R) r t)
  rw [matrix, dite_eq_left hr, rowPolynomial_subtractiveSystem, MvPolynomial.coeff_sub, MvPolynomial.coeff_map,
    MvPolynomial.coeff_monomial]
  rw [matrix, dite_eq_left hr]
  have he : FixedWidthPolynomial.vector n W r.val = FixedWidthPolynomial.vector n W t.val ↔ r = t :=
    (FixedWidthPolynomial.vector_injective n W).eq_iff.trans Subtype.val_injective.eq_iff
  by_cases hrt : r = t
  · simp only [he, Matrix.one_apply, ite_eq_left hrt, Polynomial.C_1, mul_one]
  · simp only [he, Matrix.one_apply, ite_eq_right hrt, Polynomial.C_0, mul_zero, sub_zero]

theorem activeMinor_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    activeMinor (subtractiveSystem p d) d W = AffineCharacteristic.subtractiveMatrix (activeMinor p d W) :=
  principal_subtractiveSystem p d W (activeIndices d W) (fun _ h => h)

theorem extraneousMinor_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    extraneousMinor (subtractiveSystem p d) d W = AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W) :=
  principal_subtractiveSystem p d W (extraneousIndices d W) (extraneousIndices_subset_active d W)

end LeanCanny.Algebra.Macaulay
