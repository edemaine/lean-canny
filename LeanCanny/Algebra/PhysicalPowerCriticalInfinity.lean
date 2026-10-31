/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PhysicalPowerCriticalLeading
public import LeanCanny.Algebra.HomogenizationAtInfinity

/-! # Exact equations at infinity for powered physical critical blocks

These identities concern the original source derivatives and actual frozen
height polynomials. No leading-form table is supplied by the caller.
-/

@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R K : Type*} {n : ℕ} [Fintype ι] [CommRing R] [Field K]

theorem source_infinity (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R) (a : R)
    (s : Finset (Fin (n + 1))) (normals : Fin (n + 2) → Fin (n + 1) → R)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (hlow : low.totalDegree < D) (hW : 0 < W) (y : Option (ι ⊕ Variables (n + 1)) → K) (hy : y none = 0) :
    (WeightedHomogenization.homogenize (fun _ => 1) (D * W)
      (rows (FermatCriticalHomogenization.polynomial low a D) s normals H w D W (Sum.inr 0))).eval₂ φ y =
      φ a * ∑ i, y (some (ambient i)) ^ (D * W) := by
  rw [source_split, HomogenizationAtInfinity.eval_leading φ _ _ _ (sourceLower_lt low w D W hlow hW)
    (sourceHead_homogeneous a D W) y hy]
  simp only [sourceHead, eval₂_mul, eval₂_C, eval₂_sum, eval₂_pow, eval₂_X, Function.comp_apply]

theorem gradient_infinity (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R) (a : R)
    (s : Finset (Fin (n + 1))) (normals : Fin (n + 2) → Fin (n + 1) → R)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (hD : 2 ≤ D) (hlow : low.totalDegree < D) (hW : 0 < W)
    (y : Option (ι ⊕ Variables (n + 1)) → K) (hy : y none = 0) (i : Fin (n + 1)) :
    (WeightedHomogenization.homogenize (fun _ => 1) ((D - 1) * W)
      (rows (FermatCriticalHomogenization.polynomial low a D) s normals H w D W (Sum.inl i))).eval₂ φ y =
      φ (a * (D : R)) * y (some (ambient i)) ^ ((D - 1) * W) -
        ∑ j, φ (normals j i) * y (some (multiplier j)) ^ ((D - 1) * W) := by
  rw [gradient_split, HomogenizationAtInfinity.eval_leading φ _ _ _ (gradientLower_lt low w D W hD hlow hW i)
    (gradientHead_homogeneous a normals D W i) y hy]
  simp only [gradientHead, eval₂_sub, eval₂_mul, eval₂_C, eval₂_sum, eval₂_pow, eval₂_X, Function.comp_apply]

theorem height_infinity (φ : R →+* K) (p : MvPolynomial (Fin (n + 1)) R)
    (s : Finset (Fin (n + 1))) (normals : Fin (n + 2) → Fin (n + 1) → R)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (y : Option (ι ⊕ Variables (n + 1)) → K) (hy : y none = 0) (i : Fin (n + 1)) (hi : i ∈ s)
    (hH : (CoordinatePowerSubstitution.substitute w (H i)).totalDegree < W) :
    (WeightedHomogenization.homogenize (fun _ => 1) W (rows p s normals H w D W (Sum.inr i.succ))).eval₂ φ y =
      ∑ j, φ (normals i.succ j) * y (some (ambient j)) ^ W := by
  have HL : (-(MvPolynomial.rename Sum.inl (CoordinatePowerSubstitution.substitute w (H i))) :
      MvPolynomial (ι ⊕ Variables (n + 1)) R).totalDegree < W := by
    rw [totalDegree_neg]
    exact (totalDegree_rename_le _ _).trans_lt hH
  rw [height_split p s normals H w D W i hi, HomogenizationAtInfinity.eval_leading φ _ _ _ HL
    (heightHead_homogeneous (normals i.succ) W) y hy]
  simp only [heightHead, eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Function.comp_apply]

theorem inactive_infinity (φ : R →+* K) (p : MvPolynomial (Fin (n + 1)) R)
    (s : Finset (Fin (n + 1))) (normals : Fin (n + 2) → Fin (n + 1) → R)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (y : Option (ι ⊕ Variables (n + 1)) → K) (i : Fin (n + 1)) (hi : i ∉ s) :
    (WeightedHomogenization.homogenize (fun _ => 1) ((D - 1) * W) (rows p s normals H w D W (Sum.inr i.succ))).eval₂ φ y =
      y (some (multiplier i.succ)) ^ ((D - 1) * W) := by
  rw [inactive_split p s normals H w D W i hi, WeightedHomogenization.homogenize_X_pow, eval₂_pow, eval₂_X]

end LeanCanny.Algebra.PhysicalPowerCriticalRows
