/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialAffineReparametrization
public import LeanCanny.Algebra.PolynomialSignedReflection
public import LeanCanny.Algebra.CoefficientBounds
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Affine matrix deformation and the characteristic polynomial

The determinant of A + ε(I-A) is the degree-cardinality homogeneous substitution
of det(A+sI). Its lowest order and coefficient therefore agree with those of
the characteristic polynomial of -A. All identities are division-free and
hold over an arbitrary commutative ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.AffineCharacteristic
open Polynomial
open scoped BigOperators Classical

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def additiveMatrix (A : Matrix ι ι R) : Matrix ι ι (Polynomial R) :=
  fun r s => Polynomial.C (A r s) + Polynomial.X * Polynomial.C ((1 : Matrix ι ι R) r s)

noncomputable def affineMatrix (A : Matrix ι ι R) : Matrix ι ι (Polynomial R) :=
  fun r s => Polynomial.C (A r s) + Polynomial.X *
    (Polynomial.C ((1 : Matrix ι ι R) r s) - Polynomial.C (A r s))

noncomputable def subtractiveMatrix (A : Matrix ι ι R) : Matrix ι ι (Polynomial R) :=
  fun r s => Polynomial.C (A r s) - Polynomial.X * Polynomial.C ((1 : Matrix ι ι R) r s)

theorem homogenize_det (A : Matrix ι ι (Polynomial R)) (hA : ∀ r s, (A r s).natDegree ≤ 1) :
    A.det.homogenize (Fintype.card ι) = Matrix.det (fun r s => (A r s).homogenize 1) := by
  rw [Matrix.det_apply A, Matrix.det_apply (R := MvPolynomial (Fin 2) R) (fun r s => (A r s).homogenize 1)]
  simp only [Units.smul_def, Polynomial.homogenize_finsetSum, Polynomial.homogenize_smul]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have h := Polynomial.homogenize_finsetProd (s := Finset.univ) (p := fun i => A (σ i) i) (n := fun _ => 1)
    (fun i _ => hA (σ i) i)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using h

omit [Fintype ι] in
theorem additive_entry_degree (A : Matrix ι ι R) (r s : ι) : (additiveMatrix A r s).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, Nat.add_zero] using (Polynomial.natDegree_X_le (R := R)))

theorem additive_det_degree (A : Matrix ι ι R) : (additiveMatrix A).det.natDegree ≤ Fintype.card ι := by
  have h := det_natDegree_le (additiveMatrix A) (fun _ => 1) (additive_entry_degree A)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using h

theorem additive_det_eq_charpoly_neg (A : Matrix ι ι R) : (additiveMatrix A).det = (-A).charpoly := by
  rw [Matrix.charpoly]
  congr 1
  funext r s
  rw [Matrix.charmatrix_apply]
  by_cases hrs : r = s <;> simp [additiveMatrix, Matrix.one_apply, hrs]
  ring

omit [Fintype ι] in
theorem transform_additive_entry (A : Matrix ι ι R) (r s : ι) :
    PolynomialAffineReparametrization.transform (additiveMatrix A r s) 1 = affineMatrix A r s := by
  simp only [PolynomialAffineReparametrization.transform, additiveMatrix, Polynomial.homogenize_add,
    mul_comm Polynomial.X, Polynomial.homogenize_C_mul, Polynomial.homogenize_C,
    Polynomial.homogenize_X (by decide : (1 : ℕ) ≠ 0)]
  simp [PolynomialAffineReparametrization.substitution, affineMatrix]
  ring

theorem affine_det_eq_transform (A : Matrix ι ι R) :
    (affineMatrix A).det = PolynomialAffineReparametrization.transform (additiveMatrix A).det (Fintype.card ι) := by
  change _ = PolynomialAffineReparametrization.substitution ((additiveMatrix A).det.homogenize (Fintype.card ι))
  rw [homogenize_det _ (additive_entry_degree A)]
  have hm := RingHom.map_det (R := MvPolynomial (Fin 2) R) (S := Polynomial R)
    PolynomialAffineReparametrization.substitution (fun r s => (additiveMatrix A r s).homogenize 1)
  rw [hm]
  congr 1
  funext r s
  exact (transform_additive_entry A r s).symm

theorem affine_preserves_lowest (A : Matrix ι ι R) :
    (affineMatrix A).det.natTrailingDegree = (-A).charpoly.natTrailingDegree ∧
      (affineMatrix A).det.trailingCoeff = (-A).charpoly.trailingCoeff := by
  rw [affine_det_eq_transform, ← additive_det_eq_charpoly_neg]
  exact PolynomialAffineReparametrization.preserves_lowest _ _ (additive_det_degree A)

theorem subtractive_det_eq_charpoly (A : Matrix ι ι R) :
    (subtractiveMatrix A).det = (-1 : Polynomial R) ^ Fintype.card ι * A.charpoly := by
  have hm : subtractiveMatrix A = -A.charmatrix := by
    funext r s
    rw [Matrix.neg_apply, Matrix.charmatrix_apply]
    by_cases hrs : r = s <;> simp [subtractiveMatrix, Matrix.one_apply, hrs]
  rw [hm, Matrix.det_neg]
  rfl

theorem subtractive_det_eq_comp (A : Matrix ι ι R) :
    (subtractiveMatrix A).det = (additiveMatrix A).det.comp (-Polynomial.X) := by
  have h := RingHom.map_det (R := Polynomial R) (S := Polynomial R) (Polynomial.compRingHom (-Polynomial.X)) (additiveMatrix A)
  change (additiveMatrix A).det.comp (-Polynomial.X) = _ at h
  rw [h]
  congr 1
  funext r s
  change Polynomial.C (A r s) - Polynomial.X * Polynomial.C ((1 : Matrix ι ι R) r s) =
    (Polynomial.C (A r s) + Polynomial.X * Polynomial.C ((1 : Matrix ι ι R) r s)).comp (-Polynomial.X)
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  ring

theorem subtractive_lowest (A : Matrix ι ι R) :
    (subtractiveMatrix A).det.natTrailingDegree = (affineMatrix A).det.natTrailingDegree ∧
      (subtractiveMatrix A).det.trailingCoeff =
        (-1 : R) ^ (affineMatrix A).det.natTrailingDegree * (affineMatrix A).det.trailingCoeff := by
  have ha := PolynomialAffineReparametrization.preserves_lowest (additiveMatrix A).det (Fintype.card ι) (additive_det_degree A)
  rw [← affine_det_eq_transform] at ha
  rw [subtractive_det_eq_comp]
  have hs := PolynomialSignedReflection.preserves_lowest (additiveMatrix A).det
  rw [ha.1, ha.2]
  exact hs

end LeanCanny.Algebra.AffineCharacteristic
