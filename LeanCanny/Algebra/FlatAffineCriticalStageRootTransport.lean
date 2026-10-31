/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalStage

/-! # Transporting critical roots by their evaluated affine levels

An ancestral coordinate layout may grow while the source, active constraints,
normals, and evaluated levels stay fixed. The same ambient point and multiplier
tuple then satisfy exactly the same critical-stage equations.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalStage
open MvPolynomial
open scoped Classical
variable {n : ℕ} {ι κ R K : Type*} [CommRing R] [CommRing K]

theorem roots_congr_values (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s t : Finset (Fin n)) (a c : Fin (n + 1) → Fin n → R)
    (b : Fin n → MvPolynomial ι R) (d : Fin n → MvPolynomial κ R)
    (x : ι → K) (x' : κ → K) (y : Fin n → K) (mu : Fin (n + 1) → K)
    (hs : s = t) (ha : a = c) (hb : ∀ j, (b j).eval₂ φ x = (d j).eval₂ φ x') :
    (∀ i, (row p s a b i).eval₂ φ (Sum.elim x (Sum.elim y mu)) = 0) ↔
      (∀ i, (row p t c d i).eval₂ φ (Sum.elim x' (Sum.elim y mu)) = 0) := by
  subst t
  subst c
  rw [roots_iff, roots_iff]
  simp only [Function.comp_def, ambient, multiplier, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hp, hl, hg, hu⟩
    exact ⟨hp, fun j hj => (hl j hj).trans (hb j), hg, hu⟩
  · rintro ⟨hp, hl, hg, hu⟩
    exact ⟨hp, fun j hj => (hl j hj).trans (hb j).symm, hg, hu⟩

theorem roots_congr_point (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s t : Finset (Fin n)) (a c : Fin (n + 1) → Fin n → R)
    (b : Fin n → MvPolynomial ι R) (d : Fin n → MvPolynomial κ R)
    (x : ι → K) (x' : κ → K) (v : Variables n → K)
    (hs : s = t) (ha : a = c) (hb : ∀ j, (b j).eval₂ φ x = (d j).eval₂ φ x') :
    (∀ i, (row p s a b i).eval₂ φ (Sum.elim x v) = 0) ↔
      (∀ i, (row p t c d i).eval₂ φ (Sum.elim x' v) = 0) := by
  have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
    funext j
    cases j <;> rfl
  simpa only [hv] using roots_congr_values φ p s t a c b d x x' (v ∘ Sum.inl) (v ∘ Sum.inr) hs ha hb

end LeanCanny.Algebra.FlatAffineCriticalStage
