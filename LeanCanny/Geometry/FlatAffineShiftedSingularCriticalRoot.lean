/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineSingularMultipliers

/-! # Singular points lift to critical equations with one shifted height -/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSingularCriticalRoot
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem exists_shifted_stage_root {R ι : Type*} [CommRing R] {n : ℕ}
    (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (z : Fin n → ℝ) (h : Fin n) (hs : h ∈ s) (v : ℝ)
    (hp : p.eval₂ φ z = 0)
    (hl : ∀ j ∈ s, ∑ i, φ (a j.succ i) * z i = (b j).eval₂ φ x + if j = h then v else 0)
    (hindependent : ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * φ (a j.val.succ i) = 0) → ∀ j, c j = 0)
    (hsingular : ¬Function.Surjective (derivative φ p s a z)) :
    ∃ mu : Fin (n + 1) → ℝ, mu 0 = 0 ∧
      ∀ j, (row p s a b j).eval₂ φ (Sum.elim x (Sum.elim z mu)) =
        if j = Sum.inr h.succ then v else 0 := by
  obtain ⟨mu, hz, hg, hu⟩ := exists_multipliers φ p s a z hp hindependent hsingular
  refine ⟨mu, hz, ?_⟩
  intro j
  cases j with
  | inl i =>
    simp only [row, eval_gradient, Function.comp_def, ambient, multiplier, Sum.elim_inr,
      Sum.elim_inl, hg, sub_self, Sum.inl_ne_inr, ite_false]
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · simp only [row, Fin.cases_zero, eval₂_rename, Function.comp_def, ambient,
        Sum.elim_inr, Sum.elim_inl, hp, Sum.inr.injEq, (Fin.succ_ne_zero h).symm, ite_false]
    · by_cases hjs : j ∈ s
      · have HL := hl j hjs
        simp only [row, Fin.cases_succ, ite_eq_left hjs, eval₂_sub, AffineHeightPolynomial.eval,
          eval₂_rename, Function.comp_def, ambient, Sum.elim_inr, Sum.elim_inl,
          Sum.inr.injEq, Fin.succ_inj]
        rw [HL]
        ring
      · have hjh : j ≠ h := fun he => hjs (he.symm ▸ hs)
        simp only [row, Fin.cases_succ, ite_eq_right hjs, eval₂_X, multiplier,
          Sum.elim_inr, hu j hjs, Sum.inr.injEq, Fin.succ_inj, ite_eq_right hjh]

end LeanCanny.Geometry.FlatAffineSingularCriticalRoot
