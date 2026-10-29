/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalStage
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Regular affine-height critical roots have a nonzero new multiplier

If that multiplier vanished, the source row of the spatial Jacobian would
be a combination of the active old-height rows. The resulting nonzero left
kernel vector contradicts regularity. Singular affine slices are therefore
not silently admitted as regular samples.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalRegularity
open MvPolynomial FlatAffineCriticalStage
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} {n : ℕ} [CommRing R] [CommRing K]

private theorem ambient_injective : Function.Injective (ambient (ι := ι) (n := n)) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective h)

theorem source_ambient (p : MvPolynomial (Fin n) R) (i : Fin n) :
    pderiv (ambient (ι := ι) i) (rename ambient p) = rename ambient (pderiv i p) :=
  pderiv_rename ambient_injective i p

theorem source_multiplier (p : MvPolynomial (Fin n) R) (j : Fin (n + 1)) :
    pderiv (multiplier (ι := ι) j) (rename ambient p) = 0 := by
  have hr : rename (ambient (ι := ι)) p = rename Sum.inr (rename Sum.inl p) := by
    rw [rename_rename]
    rfl
  rw [hr]
  simp only [multiplier, pderiv_rename Sum.inr_injective,
    TriangularPolynomialSystem.pderiv_inr_rename, map_zero]

theorem height_ambient (a : Fin n → R) (i : Fin n) :
    pderiv (ambient (ι := ι) i) (AffineHeightPolynomial.polynomial a ambient) = C (a i) := by
  simp [AffineHeightPolynomial.polynomial, pderiv_X, Pi.single_apply, ambient]

theorem height_multiplier (a : Fin n → R) (j : Fin (n + 1)) :
    pderiv (multiplier (ι := ι) j) (AffineHeightPolynomial.polynomial a ambient) = 0 := by
  simp [AffineHeightPolynomial.polynomial, pderiv_X, ambient, multiplier]

noncomputable def matrix (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K) :
    Matrix (Variables n) (Variables n) K :=
  fun i j => (pderiv (Sum.inr j) (row p s a b i)).eval₂ φ z

theorem matrix_source_ambient (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K) (i : Fin n) :
    matrix φ p s a b z (Sum.inr 0) (Sum.inl i) = (pderiv i p).eval₂ φ (z ∘ ambient) := by
  change (pderiv (ambient i) (rename ambient p)).eval₂ φ z = _
  rw [source_ambient, eval₂_rename]

theorem matrix_source_multiplier (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K) (j : Fin (n + 1)) :
    matrix φ p s a b z (Sum.inr 0) (Sum.inr j) = 0 := by
  change (pderiv (multiplier j) (rename ambient p)).eval₂ φ z = 0
  rw [source_multiplier, eval₂_zero]

theorem matrix_level_ambient (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K)
    (j i : Fin n) : matrix φ p s a b z (Sum.inr j.succ) (Sum.inl i) = if j ∈ s then φ (a j.succ i) else 0 := by
  by_cases hj : j ∈ s
  · simp only [matrix, row, Fin.cases_succ, ite_eq_left hj]
    change (pderiv (ambient i) (AffineHeightPolynomial.polynomial (a j.succ) ambient - rename Sum.inl (b j))).eval₂ φ z = _
    have ho : pderiv (ambient (ι := ι) i) (rename Sum.inl (b j)) = 0 :=
      TriangularPolynomialSystem.pderiv_inr_rename (b j) (Sum.inl i)
    rw [map_sub, height_ambient, ho, sub_zero, eval₂_C]
  · simp only [matrix, row, Fin.cases_succ, ite_eq_right hj]
    change (pderiv (ambient i) (X (multiplier j.succ))).eval₂ φ z = 0
    simp [ambient, multiplier, pderiv_X]

theorem matrix_level_multiplier (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K)
    (j : Fin n) (m : Fin (n + 1)) :
    matrix φ p s a b z (Sum.inr j.succ) (Sum.inr m) = if j ∈ s then 0 else if j.succ = m then 1 else 0 := by
  by_cases hj : j ∈ s
  · simp only [matrix, row, Fin.cases_succ, ite_eq_left hj]
    change (pderiv (multiplier m) (AffineHeightPolynomial.polynomial (a j.succ) ambient - rename Sum.inl (b j))).eval₂ φ z = 0
    have ho : pderiv (multiplier (ι := ι) m) (rename Sum.inl (b j)) = 0 :=
      TriangularPolynomialSystem.pderiv_inr_rename (b j) (Sum.inr m)
    rw [map_sub, height_multiplier, ho, sub_zero, eval₂_zero]
  · simp only [matrix, row, Fin.cases_succ, ite_eq_right hj]
    change (pderiv (multiplier m) (X (multiplier j.succ))).eval₂ φ z = if j.succ = m then 1 else 0
    by_cases hm : j.succ = m <;> simp [multiplier, hm, pderiv_X]

noncomputable def relation (s : Finset (Fin n)) (z : (ι ⊕ Variables n) → K) : Variables n → K
  | .inl _ => 0
  | .inr j => Fin.cases 1 (fun j => if j ∈ s then -z (multiplier j.succ) else 0) j

theorem relation_kernel (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K)
    (hg : ∀ i, (pderiv i p).eval₂ φ (z ∘ ambient) = ∑ j, φ (a j i) * z (multiplier j))
    (hu : ∀ j, j ∉ s → z (multiplier j.succ) = 0) (hz : z (multiplier 0) = 0) :
    Matrix.vecMul (relation s z) (matrix φ p s a b z) = 0 := by
  funext c
  cases c with
  | inl i =>
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, relation, zero_mul, Finset.sum_const_zero,
      zero_add, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, one_mul, matrix_source_ambient,
      matrix_level_ambient]
    have hs : (∑ j : Fin n, (if j ∈ s then -z (multiplier j.succ) else 0) *
        (if j ∈ s then φ (a j.succ i) else 0)) = - ∑ j : Fin n, φ (a j.succ i) * z (multiplier j.succ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ s
      · simp only [ite_eq_left hj]
        ring
      · simp only [ite_eq_right hj, hu j hj, mul_zero, neg_zero]
    rw [hs]
    have h := hg i
    rw [Fin.sum_univ_succ, hz, mul_zero, zero_add] at h
    rw [h, add_neg_cancel]
    rfl
  | inr m =>
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, relation, zero_mul, Finset.sum_const_zero,
      zero_add, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, one_mul, matrix_source_multiplier,
      matrix_level_multiplier]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s <;> simp [hj]

theorem multiplier_ne_zero [Nontrivial K] [NoZeroDivisors K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (s : Finset (Fin n)) (a : Fin (n + 1) → Fin n → R)
    (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K)
    (hr : ∀ j, (row p s a b j).eval₂ φ z = 0) (hdet : (matrix φ p s a b z).det ≠ 0) :
    z (multiplier 0) ≠ 0 := by
  intro hz
  have hroot := (roots_iff φ p s a b z).mp hr
  have he := Matrix.eq_zero_of_vecMul_eq_zero hdet (relation_kernel φ p s a b z hroot.2.2.1 hroot.2.2.2 hz)
  have hc := congrFun he (Sum.inr 0)
  change (1 : K) = 0 at hc
  exact one_ne_zero hc

theorem tangent_height_zero [Nontrivial K] [NoZeroDivisors K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (s : Finset (Fin n)) (a : Fin (n + 1) → Fin n → R)
    (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K)
    (hr : ∀ j, (row p s a b j).eval₂ φ z = 0) (hdet : (matrix φ p s a b z).det ≠ 0)
    (d : Fin n → K) (hp : ∑ i, (pderiv i p).eval₂ φ (z ∘ ambient) * d i = 0)
    (ha : ∀ j ∈ s, ∑ i, φ (a j.succ i) * d i = 0) : ∑ i, φ (a 0 i) * d i = 0 := by
  have hroot := (roots_iff φ p s a b z).mp hr
  have hn := multiplier_ne_zero φ p s a b z hr hdet
  have hs : (∑ i, (∑ j, φ (a j i) * z (multiplier j)) * d i) =
      ∑ j, z (multiplier j) * ∑ i, φ (a j i) * d i := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hz : (∑ j, z (multiplier j) * ∑ i, φ (a j i) * d i) = 0 := by
    rw [← hs]
    simpa only [← hroot.2.2.1] using hp
  have ho : (∑ j : Fin n, z (multiplier j.succ) * ∑ i, φ (a j.succ i) * d i) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s
    · rw [ha j hj, mul_zero]
    · rw [hroot.2.2.2 j hj, zero_mul]
  rw [Fin.sum_univ_succ, ho, add_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hn

end LeanCanny.Algebra.FlatAffineCriticalRegularity
