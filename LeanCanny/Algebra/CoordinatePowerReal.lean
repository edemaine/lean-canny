/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinatePowerSubstitution
public import LeanCanny.Algebra.FlatAffinePowerReal
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Connected.Basic

/-! # Odd coordinate powers preserve real connectivity

Coordinate-dependent odd powers form a homeomorphism of the entire ambient
real space. Polynomial substitution therefore preserves connectivity of
every real fiber, including singular fibers.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinatePowerSubstitution
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {σ : Type*}

noncomputable def realPowerHomeomorph (w : σ → ℕ) (hw : ∀ i, Odd (w i)) :
    (σ → ℝ) ≃ₜ (σ → ℝ) :=
  Homeomorph.piCongrRight (fun i =>
    (StrictMono.orderIsoOfSurjective (fun x : ℝ => x ^ w i) (hw i).strictMono_pow
      (FlatAffinePowerTower.real_pow_surjective (w i) (hw i))).toHomeomorph)

theorem realPowerHomeomorph_apply (w : σ → ℕ) (hw : ∀ i, Odd (w i)) (z : σ → ℝ) (i : σ) :
    realPowerHomeomorph w hw z i = z i ^ w i := rfl

theorem real_preconnected_iff (w : σ → ℕ) (hw : ∀ i, Odd (w i)) (S : Set (σ → ℝ)) :
    IsPreconnected ((realPowerHomeomorph w hw) ⁻¹' S) ↔ IsPreconnected S := by
  have H := (realPowerHomeomorph w hw).isInducing.isPreconnected_image
    (s := (realPowerHomeomorph w hw) ⁻¹' S)
  rw [Set.image_preimage_eq S (realPowerHomeomorph w hw).surjective] at H
  exact H.symm

theorem real_zero_set {κ : Type*} (w : σ → ℕ) (hw : ∀ i, Odd (w i)) (p : κ → MvPolynomial σ ℤ) :
    {z : σ → ℝ | ∀ i, (substitute w (p i)).eval₂ (Int.castRingHom ℝ) z = 0} =
      realPowerHomeomorph w hw ⁻¹' {z : σ → ℝ | ∀ i, (p i).eval₂ (Int.castRingHom ℝ) z = 0} := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, eval_substitute]
  rfl

end LeanCanny.Algebra.CoordinatePowerSubstitution
