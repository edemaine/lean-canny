/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulHomotopySplit
public import LeanCanny.Algebra.KoszulGenericContraction

/-! # Invariant homotopy summands of the finite contraction operators

For any homogeneous input system, `D H + H D` commutes with the normalized
raising homotopy. It therefore preserves its incoming image in every
positive weighted piece. Its canonical matrix is the previously constructed
contraction matrix. The fixed splitting can thus organize determinant
factors without choosing a basis depending on the characteristic parameter.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def homotopyOperator (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Module.End R (space (R := R) d (Macaulay.level d) W (k + 1)) :=
  (differential p d (Macaulay.level d) W hp hW (k + 1)).comp (weightedHomotopy d W hW (k + 1)) +
    (weightedHomotopy d W hW k).comp (differential p d (Macaulay.level d) W hp hW k)

theorem homotopyOperator_matrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (LinearMap.toMatrix (canonicalBasis d (Macaulay.level d) W (k + 1))
      (canonicalBasis d (Macaulay.level d) W (k + 1)) (homotopyOperator p d W hp hW k))ᵀ =
        contractionMatrix p d W hp hW k := by
  unfold homotopyOperator contractionMatrix homotopyMatrix canonicalMatrix
  rw [map_add,
    LinearMap.toMatrix_comp (canonicalBasis d (Macaulay.level d) W (k + 1))
      (canonicalBasis d (Macaulay.level d) W (k + 2)) (canonicalBasis d (Macaulay.level d) W (k + 1)),
    LinearMap.toMatrix_comp (canonicalBasis d (Macaulay.level d) W (k + 1))
      (canonicalBasis d (Macaulay.level d) W k) (canonicalBasis d (Macaulay.level d) W (k + 1)), Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.transpose_mul]

theorem homotopyOperator_comp_homotopy (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (homotopyOperator p d W hp hW (k + 1)).comp (weightedHomotopy d W hW (k + 1)) =
      (weightedHomotopy d W hW (k + 1)).comp (homotopyOperator p d W hp hW k) := by
  apply LinearMap.ext
  intro x
  change differential p d (Macaulay.level d) W hp hW (k + 2)
        (weightedHomotopy d W hW (k + 2) (weightedHomotopy d W hW (k + 1) x)) +
      weightedHomotopy d W hW (k + 1)
        (differential p d (Macaulay.level d) W hp hW (k + 1) (weightedHomotopy d W hW (k + 1) x)) =
    weightedHomotopy d W hW (k + 1)
      (differential p d (Macaulay.level d) W hp hW (k + 1) (weightedHomotopy d W hW (k + 1) x) +
        weightedHomotopy d W hW k (differential p d (Macaulay.level d) W hp hW k x))
  have hnext := LinearMap.congr_fun (weightedHomotopy_comp (R := R) d W hW (k + 1)) x
  change weightedHomotopy d W hW (k + 2) (weightedHomotopy d W hW (k + 1) x) = 0 at hnext
  have hprev := LinearMap.congr_fun (weightedHomotopy_comp (R := R) d W hW k)
    (differential p d (Macaulay.level d) W hp hW k x)
  change weightedHomotopy d W hW (k + 1)
    (weightedHomotopy d W hW k (differential p d (Macaulay.level d) W hp hW k x)) = 0 at hprev
  rw [hnext, map_zero, zero_add, map_add, hprev, add_zero]

theorem homotopyOperator_zero_apply_homotopy (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (x : space (R := R) d (Macaulay.level d) W 0) :
    homotopyOperator p d W hp hW 0 (weightedHomotopy d W hW 0 x) =
      weightedHomotopy d W hW 0
        (differential p d (Macaulay.level d) W hp hW 0 (weightedHomotopy d W hW 0 x)) := by
  change differential p d (Macaulay.level d) W hp hW 1
      (weightedHomotopy d W hW 1 (weightedHomotopy d W hW 0 x)) + _ = _
  have h := LinearMap.congr_fun (weightedHomotopy_comp (R := R) d W hW 0) x
  change weightedHomotopy d W hW 1 (weightedHomotopy d W hW 0 x) = 0 at h
  rw [h, map_zero, zero_add]
  rfl

theorem homotopyOperator_mem_range (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (x : space (R := R) d (Macaulay.level d) W (k + 1))
    (hx : x ∈ LinearMap.range (weightedHomotopy (R := R) d W hW k)) :
    homotopyOperator p d W hp hW k x ∈ LinearMap.range (weightedHomotopy (R := R) d W hW k) := by
  obtain ⟨y, rfl⟩ := hx
  cases k with
  | zero => exact ⟨_, (homotopyOperator_zero_apply_homotopy p d W hp hW y).symm⟩
  | succ k =>
    exact ⟨_, (LinearMap.congr_fun (homotopyOperator_comp_homotopy p d W hp hW k) y).symm⟩

end LeanCanny.Algebra.KoszulWeighted
