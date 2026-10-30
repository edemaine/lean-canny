/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineSingularCriticalRoot

/-! # Singular multipliers independent of the affine level values -/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSingularCriticalRoot
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem exists_multipliers {R : Type*} [CommRing R] {n : ℕ}
    (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (z : Fin n → ℝ) (hp : p.eval₂ φ z = 0)
    (hindependent : ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * φ (a j.val.succ i) = 0) → ∀ j, c j = 0)
    (hsingular : ¬Function.Surjective (derivative φ p s a z)) :
    ∃ mu : Fin (n + 1) → ℝ, mu 0 = 0 ∧
      (∀ i, (pderiv i p).eval₂ φ z = ∑ j, φ (a j i) * mu j) ∧
      ∀ j, j ∉ s → mu j.succ = 0 := by
  let b (j : Fin n) := AffineHeightPolynomial.polynomial (a j.succ) id
  obtain ⟨mu, hz, hr⟩ := exists_stage_root_of_singular φ p s a b z z hp
    (fun j _ => (AffineHeightPolynomial.eval φ (a j.succ) id z).symm) hindependent hsingular
  have H := (roots_iff φ p s a b _).mp hr
  refine ⟨mu, hz, ?_, ?_⟩
  · intro i
    exact H.2.2.1 i
  · intro j hj
    exact H.2.2.2 j hj

end LeanCanny.Geometry.FlatAffineSingularCriticalRoot
