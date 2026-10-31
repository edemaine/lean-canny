/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PhysicalPowerCriticalLeading

/-! # Derived degree bounds for actual powered critical rows

The source uses D*W, gradients and inactive multipliers use (D-1)*W,
and active heights use W. Every advertised row degree is positive and
bounded by D*W when D is at least two and W is positive.
-/

@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem row_degree (low : MvPolynomial (Fin (n + 1)) R) (a : R) (s : Finset (Fin (n + 1)))
    (normals : Fin (n + 2) → Fin (n + 1) → R) (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ)
    (D W : ℕ) (hD : 2 ≤ D) (hW : 0 < W) (hlow : low.totalDegree < D)
    (hH : ∀ i ∈ s, (CoordinatePowerSubstitution.substitute w (H i)).totalDegree < W) (j : Variables (n + 1)) :
    (rows (FermatCriticalHomogenization.polynomial low a D) s normals H w D W j).totalDegree ≤ degrees s D W j := by
  cases j with
  | inl i =>
    change _ ≤ (D - 1) * W
    rw [gradient_split]
    exact (totalDegree_add _ _).trans (max_le (gradientHead_homogeneous a normals D W i).totalDegree_le
      (gradientLower_lt low w D W hD hlow hW i).le)
  | inr j =>
    refine Fin.cases ?_ (fun i => ?_) j
    · change _ ≤ D * W
      rw [source_split]
      exact (totalDegree_add _ _).trans (max_le (sourceHead_homogeneous a D W).totalDegree_le
        (sourceLower_lt low w D W hlow hW).le)
    · by_cases hi : i ∈ s
      · simp only [degrees, Fin.cases_succ, ite_eq_left hi]
        rw [height_split _ s normals H w D W i hi]
        apply (totalDegree_add _ _).trans
        apply max_le (heightHead_homogeneous (normals i.succ) W).totalDegree_le
        rw [totalDegree_neg]
        exact (totalDegree_rename_le _ _).trans (hH i hi).le
      · simp only [degrees, Fin.cases_succ, ite_eq_right hi]
        rw [inactive_split _ s normals H w D W i hi]
        simpa only [Nat.one_mul] using
          ((isHomogeneous_X (R := R) (multiplier (ι := ι) i.succ)).pow ((D - 1) * W)).totalDegree_le

theorem degrees_pos (s : Finset (Fin (n + 1))) (D W : ℕ) (hD : 2 ≤ D) (hW : 0 < W) (j : Variables (n + 1)) :
    0 < degrees s D W j := by
  cases j with
  | inl i => exact Nat.mul_pos (by omega) hW
  | inr j =>
    refine Fin.cases (Nat.mul_pos (by omega) hW) (fun i => ?_) j
    simp only [degrees, Fin.cases_succ]
    split_ifs
    · exact hW
    · exact Nat.mul_pos (by omega) hW

theorem degrees_le (s : Finset (Fin (n + 1))) (D W : ℕ) (hD : 1 ≤ D) (j : Variables (n + 1)) :
    degrees s D W j ≤ D * W := by
  cases j with
  | inl i => exact Nat.mul_le_mul_right W (Nat.sub_le D 1)
  | inr j =>
    refine Fin.cases le_rfl (fun i => ?_) j
    simp only [degrees, Fin.cases_succ]
    split_ifs
    · simpa only [Nat.one_mul] using Nat.mul_le_mul_right W hD
    · exact Nat.mul_le_mul_right W (Nat.sub_le D 1)

end LeanCanny.Algebra.PhysicalPowerCriticalRows
