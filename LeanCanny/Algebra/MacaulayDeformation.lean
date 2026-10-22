/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayRoots
public import LeanCanny.Algebra.CoefficientBounds

/-! # A nonzero polynomial deformation of the Macaulay determinant

Interpolate each input polynomial with its coordinate power. At parameter zero
this is the original system; at parameter one the padded matrix is the identity.
Thus its determinant is a nonzero polynomial, even when the original determinant
vanishes identically. Its parameter degree is bounded by the matrix dimension.
Identifying a suitable coefficient with Canny's eliminant is still open.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open MvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def deformation (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) :
    Fin n → MvPolynomial (Fin n) (Polynomial R) := fun i =>
  (p i).map Polynomial.C + MvPolynomial.C Polynomial.X *
    (powers (R := (Polynomial R)) d i - (p i).map Polynomial.C)

theorem deformation_homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (i : Fin n) :
    (deformation p d i).IsHomogeneous (d i) := by
  have h := (hp i).map (Polynomial.C : R →+* (Polynomial R))
  have hg : (powers (R := (Polynomial R)) d i).IsHomogeneous (d i) :=
    MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_single _ _)
  exact h.add ((hg.sub h).C_mul Polynomial.X)

theorem specialization_lift (p : MvPolynomial (Fin n) R) (a : R) :
    (p.map Polynomial.C).map (Polynomial.evalRingHom a) = p := by
  have hc : (Polynomial.evalRingHom a).comp (Polynomial.C : R →+* (Polynomial R)) = RingHom.id R := by
    ext r
    simp
  rw [MvPolynomial.map_map, hc, MvPolynomial.map_id]

theorem deformation_at_one (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    (deformation p d i).map (Polynomial.evalRingHom (1 : R)) = powers d i := by
  simp only [deformation, map_add, map_mul, map_sub, MvPolynomial.map_C,
    powers, MvPolynomial.map_monomial, map_one, specialization_lift,
    Polynomial.coe_evalRingHom, Polynomial.eval_X, one_mul]
  ring

theorem deformation_at_zero (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    (deformation p d i).map (Polynomial.evalRingHom (0 : R)) = p i := by
  simp only [deformation, map_add, map_mul, map_sub, MvPolynomial.map_C,
    specialization_lift, Polynomial.coe_evalRingHom, Polynomial.eval_X, MvPolynomial.C_0, zero_mul, add_zero]

theorem matrix_deformation_at_one (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).map (Polynomial.evalRingHom (1 : R)) = 1 := by
  rw [matrix_map]
  have hf : (fun i => (deformation p d i).map (Polynomial.evalRingHom (1 : R))) = powers d :=
    funext (deformation_at_one p d)
  rw [hf, matrix_powers]

theorem det_deformation_eval_one (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).det.eval 1 = 1 := by
  change (Polynomial.evalRingHom (1 : R)) ((matrix (deformation p d) d W).det) = 1
  rw [(Polynomial.evalRingHom (1 : R)).map_det]
  change ((matrix (deformation p d) d W).map (Polynomial.evalRingHom (1 : R))).det = 1
  rw [matrix_deformation_at_one, Matrix.det_one]

theorem det_deformation_ne_zero [Nontrivial R] (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) : (matrix (deformation p d) d W).det ≠ 0 := by
  intro hz
  have h := det_deformation_eval_one p d W
  rw [hz, Polynomial.eval_zero] at h
  exact zero_ne_one h

theorem coefficient_deformation (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (i : Fin n) (e : Fin n →₀ ℕ) :
    (deformation p d i).coeff e = Polynomial.C ((p i).coeff e) + Polynomial.X *
      ((if Finsupp.single i (d i) = e then 1 else 0) - Polynomial.C ((p i).coeff e)) := by
  simp only [deformation, powers, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, MvPolynomial.coeff_map,
    MvPolynomial.coeff_monomial]

theorem coefficient_deformation_degree_le (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (i : Fin n) (e : Fin n →₀ ℕ) : ((deformation p d i).coeff e).natDegree ≤ 1 := by
  rw [coefficient_deformation]
  have hb : (((if Finsupp.single i (d i) = e then 1 else 0) : (Polynomial R)) - Polynomial.C ((p i).coeff e)).natDegree ≤ 0 := by
    split_ifs <;> exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact (Polynomial.natDegree_mul_le).trans
      ((Nat.add_le_add Polynomial.natDegree_X_le hb).trans (by decide))

theorem matrix_deformation_entry_degree_le (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r s : Index n W) : (matrix (deformation p d) d W r s).natDegree ≤ 1 := by
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · rw [entry_active _ d W r s hr]
    split_ifs
    · exact coefficient_deformation_degree_le p d _ _
    · simp
  · simp only [matrix, dite_eq_right hr, Matrix.one_apply]
    split_ifs <;> simp

theorem det_deformation_degree_le (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).det.natDegree ≤ FixedWidthPolynomial.count n W := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
    det_natDegree_le (matrix (deformation p d) d W) (fun _ => 1)
      (fun r s => matrix_deformation_entry_degree_le p d W r s)

end LeanCanny.Algebra.Macaulay
