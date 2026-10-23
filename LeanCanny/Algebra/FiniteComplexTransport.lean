/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Equiv.Basic

/-! # Exactness and surjectivity through compatible coordinates

Two adjacent commuting coordinate squares transport exactness together;
the bottom square transports surjectivity in either direction. A contracting
homotopy also gives exactness over the original coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteComplexTransport
variable {R M₀ M₁ M₂ C₀ C₁ C₂ : Type*} [CommRing R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup C₀] [Module R C₀]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]

theorem exact_of_coordinates (d : M₁ →ₗ[R] M₀) (b : M₂ →ₗ[R] M₁)
    (D : C₁ →ₗ[R] C₀) (B : C₂ →ₗ[R] C₁)
    (e₀ : M₀ ≃ₗ[R] C₀) (e₁ : M₁ ≃ₗ[R] C₁) (e₂ : M₂ ≃ₗ[R] C₂)
    (hD : ∀ x, D (e₁ x) = e₀ (d x)) (hB : ∀ x, B (e₂ x) = e₁ (b x))
    (hex : ∀ v, D v = 0 ↔ ∃ w, B w = v) : LinearMap.ker d = LinearMap.range b := by
  ext x
  change d x = 0 ↔ ∃ y, b y = x
  constructor
  · intro hx
    have hv : D (e₁ x) = 0 := by rw [hD, hx, map_zero]
    obtain ⟨w, hw⟩ := (hex _).mp hv
    refine ⟨e₂.symm w, e₁.injective ?_⟩
    rw [← hB, LinearEquiv.apply_symm_apply, hw]
  · rintro ⟨y, rfl⟩
    apply e₀.injective
    rw [map_zero, ← hD, ← hB]
    exact (hex _).mpr ⟨e₂ y, rfl⟩

theorem surjective_iff_of_coordinates (d : M₁ →ₗ[R] M₀) (D : C₁ →ₗ[R] C₀)
    (e₀ : M₀ ≃ₗ[R] C₀) (e₁ : M₁ ≃ₗ[R] C₁)
    (hD : ∀ x, D (e₁ x) = e₀ (d x)) : Function.Surjective d ↔ Function.Surjective D := by
  constructor
  · intro hd v
    obtain ⟨x, hx⟩ := hd (e₀.symm v)
    exact ⟨e₁ x, by rw [hD, hx, LinearEquiv.apply_symm_apply]⟩
  · intro hd y
    obtain ⟨x, hx⟩ := hd (e₀ y)
    refine ⟨e₁.symm x, e₀.injective ?_⟩
    rw [← hD, LinearEquiv.apply_symm_apply, hx]

theorem exact_of_homotopy (d : M₁ →ₗ[R] M₀) (b : M₂ →ₗ[R] M₁)
    (h : M₁ →ₗ[R] M₂) (j : M₀ →ₗ[R] M₁) (hdb : d.comp b = 0)
    (hid : b.comp h + j.comp d = LinearMap.id) : LinearMap.ker d = LinearMap.range b := by
  ext x
  change d x = 0 ↔ ∃ y, b y = x
  constructor
  · intro hx
    refine ⟨h x, ?_⟩
    have hi := LinearMap.congr_fun hid x
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hx, map_zero, add_zero] using hi
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hdb y

end LeanCanny.Algebra.FiniteComplexTransport
