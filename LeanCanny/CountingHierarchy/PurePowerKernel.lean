/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerDifferenceMatrix
public import LeanCanny.CountingHierarchy.PurePowerResidueRelations
public import LeanCanny.CountingHierarchy.PolynomialKernel

/-! # The normalized Bezout kernel of a pure-power system -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Matrix
open PurePowerResidue
open scoped Classical BigOperators

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The adjugate identity descends to any ideal, without requiring the
 determinant to be a unit. -/
theorem determinant_annihilates_mod_ideal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (z : ι → A) (I : Ideal A)
    (h : ∀ i, ∑ j, M i j * z j ∈ I) (j : ι) : M.det * z j ∈ I := by
  let φ := Ideal.Quotient.mk I
  have hv : M.map φ *ᵥ (fun j => φ (z j)) = 0 := by
    ext i
    change (∑ j, φ (M i j) * φ (z j)) = 0
    simp only [← map_mul]
    rw [← map_sum φ (fun j => M i j * z j)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)
  have hz := congrArg (fun v => ((M.map φ).adjugate *ᵥ v) j) hv
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_zero, Pi.zero_apply] at hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [φ, map_mul, RingHom.map_det, RingHom.mapMatrix_apply] using hz

/-- A pure-power system has an actual polynomial reproducing kernel.
 Its diagonal is the Jacobian determinant, even at multiple zeros. -/
theorem purePower_reproducing_kernel (x : Fin n → A) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) A) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hx : ∀ i, eval x (r i) = x i ^ (d + 1)) :
    ∃ K : MvPolynomial (Fin n) A,
      (∀ q, residue (d + 1) r (K * q) = eval x q) ∧
      eval x K = Matrix.det (fun i j => eval x (pderiv j (X i ^ (d + 1) - r i))) := by
  obtain ⟨W, hrow, hdegree, htop, hdiag⟩ := purePower_difference_matrix x d hd r hr hx
  have hell : 1 ≤ d + 1 := by omega
  have hr' (i : Fin n) : (r i).totalDegree < d + 1 := by have := hr i; omega
  have hnormal : residue (d + 1) r W.det = 1 := by
    rw [residue_low_degree hell r hr' W.det (by
      simpa only [Nat.add_sub_cancel] using polynomial_det_degree_le W d hdegree)]
    have hN (i j : Fin n) :
        (Matrix.diagonal (fun j => (X j : MvPolynomial (Fin n) A) ^ d) i j).totalDegree ≤ d := by
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq, X_pow_eq_monomial]
        exact (totalDegree_monomial_le _ _).trans (by simp)
      · simp only [Matrix.diagonal_apply_ne _ hij, totalDegree_zero]
        omega
    have he : n * d ≤ (exponent (fun _ : Fin n => d)).degree := by
      change n * d ≤ (exponent (fun _ : Fin n => d)).sum (fun _ e => e)
      rw [Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := polynomial_det_top_coefficient W (Matrix.diagonal (fun j => X j ^ d))
      d hdegree hN htop (exponent (fun _ => d)) he
    have hp : (∏ i : Fin n, (X i : MvPolynomial (Fin n) A) ^ d) =
        monomial (exponent (fun _ => d)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    simp only [Nat.add_sub_cancel, hc, Matrix.det_diagonal, hp, coeff_monomial,
      ↓reduceIte]
  have hann (j : Fin n) : W.det * (C (x j) - X j) ∈ relationIdeal (d + 1) r := by
    apply determinant_annihilates_mod_ideal W _ _ (fun i => ?_) j
    rw [hrow]
    apply (relationIdeal (d + 1) r).neg_mem
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨W.det, ?_, ?_⟩
  · intro q
    apply polynomial_kernel_reproduces (linear hell r hr') W.det x hnormal ?_ q
    intro i v
    apply linear_mem_ideal hell r hr'
    have hh := (relationIdeal (d + 1) r).mul_mem_left v (hann i)
    have heq : W.det * v * (X i - C (x i)) = -(v * (W.det * (C (x i) - X i))) := by ring
    rw [heq]
    exact (relationIdeal (d + 1) r).neg_mem hh
  · rw [RingHom.map_det]
    congr 1
    ext i j
    exact hdiag i j

end LeanCanny.CountingHierarchy
