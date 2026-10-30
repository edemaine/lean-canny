/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ComponentFiberCriticalMaximum
public import LeanCanny.Geometry.FlatAffineComponentSampling
public import LeanCanny.Geometry.FlatAffineSingularCriticalCharacterization

/-! # Critical roots meet every component of a compact affine slice

A component maximum gives normalized multipliers at a regular point and
zero-objective multipliers at a singular point. Independent slice normals
therefore give complete component samples without global slice regularity.
The conclusion concerns connected components, with no assertion that a
singular component is path connected.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSingularComponentSampling
open Set LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem exists_component_stage_root (phi : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ)
    (hcompact : IsCompact {y : Fin n → ℝ | p.eval₂ phi y = 0 ∧
      ∀ j ∈ s, ∑ i, phi (a j.succ i) * y i = (b j).eval₂ phi x})
    (hheights : ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * phi (a j.val.succ i) = 0) → ∀ j, c j = 0)
    (hindependent : ¬∃ c : s → ℝ, ∀ i, phi (a 0 i) = ∑ j : s, c j * phi (a j.val.succ i))
    (z : Fin n → ℝ) (hp : p.eval₂ phi z = 0)
    (hl : ∀ j ∈ s, ∑ i, phi (a j.succ i) * z i = (b j).eval₂ phi x) :
    ∃ (y : Fin n → ℝ) (mu : Fin (n + 1) → ℝ),
      y ∈ connectedComponentIn {v | p.eval₂ phi v = 0 ∧ ∀ j ∈ s,
        ∑ i, phi (a j.succ i) * v i = (b j).eval₂ phi x} z ∧
      ∀ j, (row p s a b j).eval₂ phi (Sum.elim x (Sum.elim y mu)) = 0 := by
  let g : (Fin n → ℝ) → (Option s → ℝ) := fun y j => (constraint p s a j).eval₂ phi y
  have hsmooth : ContDiff ℝ ⊤ g := contDiff_pi.mpr
    (fun j => ProjectionCritical.contDiff_eval phi (constraint p s a j))
  have hd (y : Fin n → ℝ) : fderiv ℝ g y = derivative phi p s a y := by
    apply HasFDerivAt.fderiv
    exact hasFDerivAt_pi.mpr (fun j => PolynomialCalculus.hasFDerivAt phi (constraint p s a j) y)
  have he : {y | g y = g z} = {y : Fin n → ℝ | p.eval₂ phi y = 0 ∧
      ∀ j ∈ s, ∑ i, phi (a j.succ i) * y i = (b j).eval₂ phi x} := fiber_eq_slice phi p s a b x z hp hl
  obtain ⟨y, hy, hc, hs⟩ := ComponentFiberCriticalMaximum.exists_component_critical_max g (g z)
    (ProjectionCritical.projection (fun i => phi (a 0 i)))
    (fun _ => hsmooth.contDiffAt.of_le le_top) (he.symm ▸ hcompact)
    (ProjectionCritical.projection _).continuous z rfl
  have hy' : y ∈ {v : Fin n → ℝ | p.eval₂ phi v = 0 ∧
      ∀ j ∈ s, ∑ i, phi (a j.succ i) * v i = (b j).eval₂ phi x} := he ▸ hy
  rw [he] at hc
  rcases hs with hsingular | ⟨hregular, hmax⟩
  · obtain ⟨mu, _, hroot⟩ := FlatAffineSingularCriticalRoot.exists_stage_root_of_singular phi p s a b x y
      hy'.1 hy'.2 hheights (by rwa [← hd])
    exact ⟨y, mu, hc, hroot⟩
  · rw [he] at hmax
    obtain ⟨mu, _, hroot⟩ := exists_stage_root_on_slice phi p s a b x y hy'.1 hy'.2 hmax
      (by rwa [← hd]) hindependent
    exact ⟨y, mu, hc, hroot⟩

end LeanCanny.Geometry.FlatAffineSingularComponentSampling
