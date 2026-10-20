/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulHomotopyNormalization
public import Mathlib.LinearAlgebra.Projection

/-! # A fixed splitting of each positive weighted Koszul piece

The pure-power differential and normalized polynomial homotopy give
complementary projections. Each positive piece is the direct sum of the
incoming homotopy image and incoming pure-power differential image. This
splitting is defined over the original coefficient ring and is independent
of the shifted input system.
-/

@[expose] public section

namespace LeanCanny.Algebra.ComplementaryEndomorphisms
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem isCompl_range (P Q : M →ₗ[R] M) (hs : P + Q = LinearMap.id) (hz : P.comp Q = 0) :
    IsCompl (LinearMap.range P) (LinearMap.range Q) := by
  have hp : IsIdempotentElem P := by
    change P.comp P = P
    calc
      P.comp P = P.comp P + P.comp Q := by rw [hz, add_zero]
      _ = P.comp (P + Q) := by rw [LinearMap.comp_add]
      _ = P := by rw [hs, LinearMap.comp_id]
  have hk : LinearMap.ker P = LinearMap.range Q := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      have h := LinearMap.congr_fun hs x
      change P x + Q x = x at h
      rw [hx, zero_add] at h
      exact h
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun hz y
  rw [← hk]
  exact LinearMap.IsIdempotentElem.isCompl hp

end LeanCanny.Algebra.ComplementaryEndomorphisms

namespace LeanCanny.Algebra.KoszulWeighted
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def homotopyProjection (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Module.End R (space (R := R) d (Macaulay.level d) W (k + 1)) :=
  (weightedHomotopy d W hW k).comp
    (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k)

noncomputable def powerProjection (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Module.End R (space (R := R) d (Macaulay.level d) W (k + 1)) :=
  (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)).comp
    (weightedHomotopy d W hW (k + 1))

theorem projections_add (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    homotopyProjection (R := R) d W hW k + powerProjection (R := R) d W hW k = LinearMap.id := by
  exact (add_comm _ _).trans (weightedHomotopy_identity d W hW k)

theorem projections_comp (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (homotopyProjection (R := R) d W hW k).comp (powerProjection (R := R) d W hW k) = 0 := by
  apply LinearMap.ext
  intro x
  change weightedHomotopy (R := R) d W hW k
    (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k
      (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)
        (weightedHomotopy (R := R) d W hW (k + 1) x))) = 0
  rw [show differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k
      (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)
        (weightedHomotopy (R := R) d W hW (k + 1) x)) = 0 from
    LinearMap.congr_fun (differential_comp (Macaulay.powers (R := R) d) d (Macaulay.level d) W
      (powers_homogeneous d) hW k) _, map_zero]

theorem range_homotopyProjection (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.range (homotopyProjection (R := R) d W hW k) = LinearMap.range (weightedHomotopy (R := R) d W hW k) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨weightedHomotopy (R := R) d W hW k y, ?_⟩
    have h := LinearMap.congr_fun (weightedHomotopy_identity (R := R) d W hW k)
      (weightedHomotopy (R := R) d W hW k y)
    have hz := LinearMap.congr_fun (weightedHomotopy_comp (R := R) d W hW k) y
    change weightedHomotopy (R := R) d W hW (k + 1) (weightedHomotopy (R := R) d W hW k y) = 0 at hz
    change differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)
        (weightedHomotopy (R := R) d W hW (k + 1) (weightedHomotopy (R := R) d W hW k y)) +
      homotopyProjection (R := R) d W hW k (weightedHomotopy (R := R) d W hW k y) = _ at h
    rw [hz, map_zero, zero_add] at h
    exact h

theorem range_powerProjection (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.range (powerProjection (R := R) d W hW k) =
      LinearMap.range (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    let x := differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1) y
    refine ⟨x, ?_⟩
    have h := LinearMap.congr_fun (projections_add (R := R) d W hW k) x
    have hz : homotopyProjection (R := R) d W hW k x = 0 := by
      change weightedHomotopy (R := R) d W hW k
        (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k x) = 0
      rw [show differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k x = 0 from
        LinearMap.congr_fun (differential_comp (Macaulay.powers (R := R) d) d (Macaulay.level d) W
          (powers_homogeneous d) hW k) y, map_zero]
    change homotopyProjection (R := R) d W hW k x + powerProjection (R := R) d W hW k x = x at h
    rw [hz, zero_add] at h
    exact h

theorem homotopy_power_isCompl (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    IsCompl (LinearMap.range (weightedHomotopy (R := R) d W hW k))
      (LinearMap.range (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1))) := by
  rw [← range_homotopyProjection, ← range_powerProjection]
  exact ComplementaryEndomorphisms.isCompl_range _ _ (projections_add d W hW k) (projections_comp d W hW k)

noncomputable def pieceSplit (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (LinearMap.range (weightedHomotopy (R := R) d W hW k) ×
      LinearMap.range (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1))) ≃ₗ[R]
        space (R := R) d (Macaulay.level d) W (k + 1) :=
  Submodule.prodEquivOfIsCompl _ _ (homotopy_power_isCompl d W hW k)

end LeanCanny.Algebra.KoszulWeighted
