/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineCriticalExtremum
public import LeanCanny.Geometry.ComponentFiberMaximum

/-! # Affine critical roots sample components of compact regular slices

Every point can reach a stage root in its own affine-slice component.
Regularity here concerns the slice constraint map. Regularity of the larger
critical stage, needed by native regular-root sampling, is a separate condition.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineComponentSampling
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem exists_joined_stage_root (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ)
    (hcompact : IsCompact {y : Fin n → ℝ | p.eval₂ φ y = 0 ∧
      ∀ j ∈ s, ∑ i, φ (a j.succ i) * y i = (b j).eval₂ φ x})
    (hregular : ∀ y : Fin n → ℝ, p.eval₂ φ y = 0 →
      (∀ j ∈ s, ∑ i, φ (a j.succ i) * y i = (b j).eval₂ φ x) →
      Function.Surjective (derivative φ p s a y))
    (hindependent : ¬ ∃ c : s → ℝ, ∀ i, φ (a 0 i) = ∑ j : s, c j * φ (a j.val.succ i))
    (z : Fin n → ℝ) (hp : p.eval₂ φ z = 0)
    (hl : ∀ j ∈ s, ∑ i, φ (a j.succ i) * z i = (b j).eval₂ φ x) :
    ∃ (y : Fin n → ℝ) (μ : Fin (n + 1) → ℝ), μ 0 ≠ 0 ∧
      JoinedIn {v | p.eval₂ φ v = 0 ∧ ∀ j ∈ s, ∑ i, φ (a j.succ i) * v i = (b j).eval₂ φ x} z y ∧
      ∀ j, (row p s a b j).eval₂ φ (Sum.elim x (Sum.elim y μ)) = 0 := by
  let g : (Fin n → ℝ) → (Option s → ℝ) := fun y j => (constraint p s a j).eval₂ φ y
  have hsmooth : ContDiff ℝ ⊤ g := contDiff_pi.mpr
    (fun j => ProjectionCritical.contDiff_eval φ (constraint p s a j))
  have hd (y : Fin n → ℝ) : fderiv ℝ g y = derivative φ p s a y := by
    apply HasFDerivAt.fderiv
    exact hasFDerivAt_pi.mpr (fun j => PolynomialCalculus.hasFDerivAt φ (constraint p s a j) y)
  have he : {y | g y = g z} = {y : Fin n → ℝ | p.eval₂ φ y = 0 ∧
      ∀ j ∈ s, ∑ i, φ (a j.succ i) * y i = (b j).eval₂ φ x} := fiber_eq_slice φ p s a b x z hp hl
  have hc : IsCompact {y | g y = g z} := he.symm ▸ hcompact
  have hr : ∀ y : RegularFiber.Fiber g (g z), Function.Surjective (fderiv ℝ g y.val) := by
    intro y
    have hy : y.val ∈ {v : Fin n → ℝ | p.eval₂ φ v = 0 ∧
        ∀ j ∈ s, ∑ i, φ (a j.succ i) * v i = (b j).eval₂ φ x} := he ▸ y.property
    rw [hd]
    exact hregular y.val hy.1 hy.2
  obtain ⟨y, hy, hj, hm⟩ := ComponentFiberMaximum.exists_joined_localMax g (g z)
    (ProjectionCritical.projection (fun i => φ (a 0 i)))
    (fun _ => hsmooth.contDiffAt.of_le le_top) hr hc
    (ProjectionCritical.projection _).continuous z rfl
  have hy' : y ∈ {v : Fin n → ℝ | p.eval₂ φ v = 0 ∧
      ∀ j ∈ s, ∑ i, φ (a j.succ i) * v i = (b j).eval₂ φ x} := he ▸ hy
  rw [he] at hj hm
  obtain ⟨μ, hμ, hroot⟩ := exists_stage_root_on_slice φ p s a b x y hy'.1 hy'.2 hm
    (hregular y hy'.1 hy'.2) hindependent
  exact ⟨y, μ, hμ, hj, hroot⟩

end LeanCanny.Geometry.FlatAffineComponentSampling
