/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PhysicalPowerCriticalRows
public import LeanCanny.Algebra.CoordinatePowerRename
public import LeanCanny.Algebra.FermatCriticalHomogenization

/-! # Leading forms of the actual powered critical equations

The original source has Fermat-leading degree D. Spatial variables use W
and multipliers use (D-1)*W. A substituted height of degree below W changes
only the lower part. Derivatives are taken before all power substitutions.
-/

@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage CoordinatePowerSubstitution
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} {n : ℕ} [CommRing R]

noncomputable def sourceHead (a : R) (D W : ℕ) : MvPolynomial (ι ⊕ Variables (n + 1)) R :=
  C a * ∑ i : Fin (n + 1), X (ambient i) ^ (D * W)

noncomputable def gradientHead (a : R) (normals : Fin (n + 2) → Fin (n + 1) → R)
    (D W : ℕ) (i : Fin (n + 1)) : MvPolynomial (ι ⊕ Variables (n + 1)) R :=
  C (a * (D : R)) * X (ambient i) ^ ((D - 1) * W) -
    ∑ j, C (normals j i) * X (multiplier j) ^ ((D - 1) * W)

noncomputable def heightHead (normal : Fin (n + 1) → R) (W : ℕ) : MvPolynomial (ι ⊕ Variables (n + 1)) R :=
  ∑ i, C (normal i) * X (ambient i) ^ W

noncomputable def spatialLower (low : MvPolynomial (Fin (n + 1)) R) (w : ι → ℕ) (D W : ℕ) :
    MvPolynomial (ι ⊕ Variables (n + 1)) R := substitute (powers w D W) (MvPolynomial.rename ambient low)

theorem source_split (low : MvPolynomial (Fin (n + 1)) R) (a : R) (s : Finset (Fin (n + 1)))
    (normals : Fin (n + 2) → Fin (n + 1) → R) (H : Fin (n + 1) → MvPolynomial ι R)
    (w : ι → ℕ) (D W : ℕ) :
    rows (FermatCriticalHomogenization.polynomial low a D) s normals H w D W (Sum.inr 0) =
      sourceHead a D W + spatialLower low w D W := by
  simp only [rows, row, Fin.cases_zero, FermatCriticalHomogenization.polynomial,
    map_add, map_mul, rename_C, map_sum, map_pow, rename_X, substitute_C, substitute_X,
    powers, ambient, ← pow_mul, Nat.mul_comm W D, sourceHead, spatialLower]
  exact add_comm _ _

theorem gradient_split (low : MvPolynomial (Fin (n + 1)) R) (a : R) (s : Finset (Fin (n + 1)))
    (normals : Fin (n + 2) → Fin (n + 1) → R) (H : Fin (n + 1) → MvPolynomial ι R)
    (w : ι → ℕ) (D W : ℕ) (i : Fin (n + 1)) :
    rows (FermatCriticalHomogenization.polynomial low a D) s normals H w D W (Sum.inl i) =
      gradientHead a normals D W i + spatialLower (pderiv i low) w D W := by
  simp only [rows, row, gradient, FermatCriticalHomogenization.pderiv_polynomial,
    map_sub, map_add, map_mul, rename_C, map_sum, map_pow, rename_X, substitute_C, substitute_X,
    powers, ambient, multiplier, ← pow_mul, Nat.mul_comm W (D - 1), gradientHead, spatialLower]
  ring

theorem height_split (p : MvPolynomial (Fin (n + 1)) R) (s : Finset (Fin (n + 1)))
    (normals : Fin (n + 2) → Fin (n + 1) → R) (H : Fin (n + 1) → MvPolynomial ι R)
    (w : ι → ℕ) (D W : ℕ) (i : Fin (n + 1)) (hi : i ∈ s) :
    rows p s normals H w D W (Sum.inr i.succ) = heightHead (normals i.succ) W +
      -(MvPolynomial.rename Sum.inl (substitute w (H i))) := by
  rw [rows, row, Fin.cases_succ, ite_eq_left hi, map_sub, CoordinatePowerSubstitution.rename]
  simp only [AffineHeightPolynomial.polynomial, map_sum, map_mul, substitute_C, substitute_X,
    powers, ambient, heightHead]
  have HE : powers (n := n + 1) w D W ∘ Sum.inl = w := rfl
  rw [HE, sub_eq_add_neg]

theorem inactive_split (p : MvPolynomial (Fin (n + 1)) R) (s : Finset (Fin (n + 1)))
    (normals : Fin (n + 2) → Fin (n + 1) → R) (H : Fin (n + 1) → MvPolynomial ι R)
    (w : ι → ℕ) (D W : ℕ) (i : Fin (n + 1)) (hi : i ∉ s) :
    rows p s normals H w D W (Sum.inr i.succ) = X (multiplier i.succ) ^ ((D - 1) * W) := by
  simp only [rows, row, Fin.cases_succ, ite_eq_right hi, substitute_X, powers, multiplier]

theorem spatialLower_degree (low : MvPolynomial (Fin (n + 1)) R) (w : ι → ℕ) (D W : ℕ) :
    (spatialLower low w D W).totalDegree ≤ W * low.totalDegree :=
  CoordinatePowerSubstitution.rename_degree _ ambient low W (fun _ => le_rfl)

theorem sourceLower_lt (low : MvPolynomial (Fin (n + 1)) R) (w : ι → ℕ) (D W : ℕ)
    (hlow : low.totalDegree < D) (hW : 0 < W) : (spatialLower low w D W).totalDegree < D * W :=
  ((spatialLower_degree low w D W).trans_lt (Nat.mul_lt_mul_of_pos_left hlow hW)).trans_eq (Nat.mul_comm _ _)

theorem gradientLower_lt (low : MvPolynomial (Fin (n + 1)) R) (w : ι → ℕ) (D W : ℕ)
    (hD : 2 ≤ D) (hlow : low.totalDegree < D) (hW : 0 < W) (i : Fin (n + 1)) :
    (spatialLower (pderiv i low) w D W).totalDegree < (D - 1) * W := by
  have HD : (pderiv i low).totalDegree < D - 1 := (PartialDerivativeDegree.degree_le low i).trans_lt (by omega)
  exact ((spatialLower_degree _ w D W).trans_lt (Nat.mul_lt_mul_of_pos_left HD hW)).trans_eq (Nat.mul_comm _ _)

theorem sourceHead_homogeneous (a : R) (D W : ℕ) : (sourceHead (ι := ι) (n := n) a D W).IsHomogeneous (D * W) := by
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  simpa only [Nat.one_mul] using (isHomogeneous_X (R := R) (ambient (ι := ι) i)).pow (D * W)

theorem gradientHead_homogeneous (a : R) (normals : Fin (n + 2) → Fin (n + 1) → R)
    (D W : ℕ) (i : Fin (n + 1)) : (gradientHead (ι := ι) a normals D W i).IsHomogeneous ((D - 1) * W) := by
  apply IsHomogeneous.sub
  · simpa only [Nat.one_mul] using ((isHomogeneous_X (R := R) (ambient (ι := ι) i)).pow ((D - 1) * W)).C_mul (a * (D : R))
  · apply IsHomogeneous.sum
    intro j _
    simpa only [Nat.one_mul] using ((isHomogeneous_X (R := R) (multiplier (ι := ι) j)).pow ((D - 1) * W)).C_mul (normals j i)

theorem heightHead_homogeneous (normal : Fin (n + 1) → R) (W : ℕ) :
    (heightHead (ι := ι) normal W).IsHomogeneous W := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [Nat.one_mul] using ((isHomogeneous_X (R := R) (ambient (ι := ι) i)).pow W).C_mul (normal i)

end LeanCanny.Algebra.PhysicalPowerCriticalRows
