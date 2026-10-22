/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayCharacteristic
public import LeanCanny.Algebra.MacaulayDeformationParameters
public import LeanCanny.Algebra.PrincipalPadding

/-! # The extraneous principal minor of the Macaulay matrix

At the Macaulay level, unreduced monomials are divisible by at least two of
the designated coordinate powers. The extraneous matrix is the principal
submatrix on those indices. Identity padding represents its determinant on
the original fixed-width index set, commutes with deformation, and gives a
nonzero deformation polynomial with value one at parameter one.

The resultant quotient formula is not asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical

variable {n : ℕ} {R : Type*} [CommRing R]

def Unreduced (d : Fin n → ℕ) (e : Fin n →₀ ℕ) : Prop := 1 < (eligible d e).card

theorem unreduced_iff (d : Fin n → ℕ) (e : Fin n →₀ ℕ) :
    Unreduced d e ↔ ∃ i j, i ≠ j ∧ d i ≤ e i ∧ d j ≤ e j := by
  simp only [Unreduced, Finset.one_lt_card, eligible, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, j, hj, hij⟩
    exact ⟨i, j, hij, hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨i, hi, j, hj, hij⟩

noncomputable def extraneousIndices (d : Fin n → ℕ) (W : ℕ) : Finset (Index n W) :=
  Finset.univ.filter (fun r => (FixedWidthPolynomial.vector n W r).degree = level d ∧
    Unreduced d (FixedWidthPolynomial.vector n W r))

theorem mem_extraneousIndices (d : Fin n → ℕ) (W : ℕ) (r : Index n W) :
    r ∈ extraneousIndices d W ↔ (FixedWidthPolynomial.vector n W r).degree = level d ∧
      Unreduced d (FixedWidthPolynomial.vector n W r) := by
  simp only [extraneousIndices, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def extraneousMinor (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :=
  (matrix p d W).submatrix (fun i : extraneousIndices d W => i.val) (fun i : extraneousIndices d W => i.val)

noncomputable def extraneousPadded (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Matrix (Index n W) (Index n W) R := PrincipalPadding.matrix (matrix p d W) (extraneousIndices d W)

theorem extraneousPadded_det (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousPadded p d W).det = (extraneousMinor p d W).det :=
  PrincipalPadding.determinant _ _

theorem extraneousPadded_powers (d : Fin n → ℕ) (W : ℕ) : extraneousPadded (powers (R := R) d) d W = 1 := by
  rw [extraneousPadded, matrix_powers, PrincipalPadding.matrix_one]

theorem extraneous_deformation_eq_affine (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    extraneousPadded (deformation p d) d W = AffineCharacteristic.affineMatrix (extraneousPadded p d W) := by
  rw [extraneousPadded, matrix_deformation_eq_affine, PrincipalPadding.matrix_affine]
  rfl

theorem extraneous_deformation_eval_one (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousPadded (deformation p d) d W).det.eval 1 = 1 := by
  change (Polynomial.evalRingHom (1 : R)) ((extraneousPadded (deformation p d) d W).det) = 1
  rw [RingHom.map_det]
  change ((extraneousPadded (deformation p d) d W).map (Polynomial.evalRingHom (1 : R))).det = 1
  rw [extraneousPadded, PrincipalPadding.matrix_map, matrix_deformation_at_one, PrincipalPadding.matrix_one, Matrix.det_one]

theorem extraneous_deformation_ne_zero [Nontrivial R] (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousPadded (deformation p d) d W).det ≠ 0 := by
  intro hz
  have h := extraneous_deformation_eval_one p d W
  rw [hz, Polynomial.eval_zero] at h
  exact zero_ne_one h

theorem extraneous_deformation_map {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousPadded (deformation p d) d W).map (Polynomial.mapRingHom φ) =
      extraneousPadded (deformation (fun i => (p i).map φ) d) d W := by
  rw [extraneousPadded, PrincipalPadding.matrix_map, matrix_deformation_map]
  rfl

theorem det_extraneous_deformation_map {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousPadded (deformation p d) d W).det.map φ =
      (extraneousPadded (deformation (fun i => (p i).map φ) d) d W).det := by
  have h := RingHom.map_det (R := Polynomial R) (S := Polynomial S) (Polynomial.mapRingHom φ)
    (extraneousPadded (deformation p d) d W)
  change (extraneousPadded (deformation p d) d W).det.map φ =
    ((extraneousPadded (deformation p d) d W).map (Polynomial.mapRingHom φ)).det at h
  rw [extraneous_deformation_map] at h
  exact h

theorem extraneous_deformation_inner_degree {K : Type*} [CommRing K]
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial K))) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e k, (((p i).coeff e).coeff k).natDegree ≤ E) (j k : ℕ) :
    (((extraneousPadded (deformation p d) d W).det.coeff j).coeff k).natDegree ≤ FixedWidthPolynomial.count n W * E := by
  have hentry (r s : Index n W) (a b : ℕ) :
      ((((extraneousPadded (deformation p d) d W) r s).coeff a).coeff b).natDegree ≤ E := by
    change (((if r ∈ extraneousIndices d W then matrix (deformation p d) d W r s else
      (1 : Matrix (Index n W) (Index n W) (Polynomial (Polynomial (Polynomial K)))) r s).coeff a).coeff b).natDegree ≤ E
    by_cases hr : r ∈ extraneousIndices d W
    · rw [ite_eq_left hr]
      exact matrix_deformation_inner_degree p d W E hp r s a b
    · rw [ite_eq_right hr]
      by_cases hrs : r = s <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
        simp [Matrix.one_apply, hrs, ha, hb, Polynomial.coeff_one]
  have h := PolynomialTripleDegree.determinant_degree (extraneousPadded (deformation p d) d W) (fun _ => E) hentry j k
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem extraneous_characteristic_lowest (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det.natTrailingDegree =
      (extraneousPadded (deformation p d) d W).det.natTrailingDegree ∧
    (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det.trailingCoeff =
      (-1 : R) ^ (extraneousPadded (deformation p d) d W).det.natTrailingDegree *
        (extraneousPadded (deformation p d) d W).det.trailingCoeff := by
  rw [extraneous_deformation_eq_affine]
  have hm := PrincipalPadding.characteristic_lowest (matrix p d W) (extraneousIndices d W)
  have hp := AffineCharacteristic.subtractive_lowest (extraneousPadded p d W)
  exact ⟨hm.1.symm.trans hp.1, hm.2.symm.trans hp.2⟩

end LeanCanny.Algebra.Macaulay
