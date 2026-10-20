/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayAffineDeformation
public import LeanCanny.Algebra.MacaulayBivariateBounds
public import LeanCanny.Algebra.PolynomialTripleDegree

/-! # Deformation with independent coefficient parameters

Coefficient maps preserve the new deformation variable. The original two
parameters stay independent, with an inner-degree bound for every coefficient
of the deformation determinant. This permits bounded encodings without merging
the deformation parameter with a parameter of the original system.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical

theorem deformation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    (deformation p d i).map (Polynomial.mapRingHom φ) = deformation (fun j => (p j).map φ) d i := by
  have hc : (Polynomial.mapRingHom φ).comp Polynomial.C = Polynomial.C.comp φ := by
    ext a
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
  simp only [deformation, map_add, map_mul, map_sub, MvPolynomial.map_C, MvPolynomial.map_map, powers,
    MvPolynomial.map_monomial, map_one, hc, Polynomial.coe_mapRingHom, Polynomial.map_X]

theorem matrix_deformation_at_zero {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).map (Polynomial.evalRingHom (0 : R)) = matrix p d W := by
  rw [matrix_map]
  congr 1
  funext i
  exact deformation_at_zero p d i

theorem det_deformation_eval_zero {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).det.eval 0 = (matrix p d W).det := by
  change (Polynomial.evalRingHom (0 : R)) ((matrix (deformation p d) d W).det) = _
  rw [(Polynomial.evalRingHom (0 : R)).map_det]
  change ((matrix (deformation p d) d W).map (Polynomial.evalRingHom (0 : R))).det = _
  rw [matrix_deformation_at_zero]

theorem matrix_deformation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).map (Polynomial.mapRingHom φ) =
      matrix (deformation (fun i => (p i).map φ) d) d W := by
  rw [matrix_map]
  congr 1
  funext i
  exact deformation_map φ p d i

theorem det_deformation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix (deformation p d) d W).det.map φ = (matrix (deformation (fun i => (p i).map φ) d) d W).det := by
  have h := RingHom.map_det (R := Polynomial R) (S := Polynomial S) (Polynomial.mapRingHom φ) (matrix (deformation p d) d W)
  change (matrix (deformation p d) d W).det.map φ = ((matrix (deformation p d) d W).map (Polynomial.mapRingHom φ)).det at h
  rw [matrix_deformation_map] at h
  exact h

theorem matrix_deformation_inner_degree {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial R))) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e k, (((p i).coeff e).coeff k).natDegree ≤ E) (r s : Index n W) (j k : ℕ) :
    ((((matrix (deformation p d) d W r s).coeff j).coeff k).natDegree) ≤ E := by
  have hA := matrix_inner_degree p d W E hp r s k
  have hI : (((1 : Matrix (Index n W) (Index n W) (Polynomial (Polynomial R))) r s).coeff k).natDegree ≤ E := by
    by_cases hrs : r = s <;> by_cases hk : k = 0 <;> simp [Matrix.one_apply, hrs, hk, Polynomial.coeff_one]
  rw [matrix_deformation_coefficient]
  split_ifs
  · exact hA
  · rw [Polynomial.coeff_sub]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hI hA)
  · simp

theorem det_deformation_inner_degree {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial R))) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e k, (((p i).coeff e).coeff k).natDegree ≤ E) (j k : ℕ) :
    ((((matrix (deformation p d) d W).det.coeff j).coeff k).natDegree) ≤ FixedWidthPolynomial.count n W * E := by
  have h := PolynomialTripleDegree.determinant_degree (matrix (deformation p d) d W) (fun _ => E)
    (matrix_deformation_inner_degree p d W E hp) j k
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem det_deformation_encode_coefficient {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial ℤ))) (d : Fin n → ℕ) (W E B : ℕ)
    (hp : ∀ i e k, (((p i).coeff e).coeff k).natDegree ≤ E)
    (hB : FixedWidthPolynomial.count n W * E < B) (i j k : ℕ) (hi : i < B) :
    ((Polynomial.map (PolynomialKronecker.encode B) (matrix (deformation p d) d W).det).coeff j).coeff (i + B * k) =
      (((matrix (deformation p d) d W).det.coeff j).coeff k).coeff i := by
  rw [Polynomial.coeff_map]
  exact PolynomialKronecker.coefficient B _ (fun k => (det_deformation_inner_degree p d W E hp j k).trans_lt hB) i k hi

end LeanCanny.Algebra.Macaulay
