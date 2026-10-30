/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineComponentSampling
public import LeanCanny.Algebra.FlatAffineShiftedLevels

/-! # Critical roots sample every component of a regular varying-height slice

An extra frozen coordinate represents the varied level. The regular-slice
maximum theorem applies to this exact slice and gives paths to shifted
critical roots, with a nonzero objective multiplier.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineShiftedComponentSampling
open Set LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} {n : ℕ} [CommRing R]

noncomputable def slice (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (h : Fin n) (v : ℝ) : Set (Fin n → ℝ) :=
  {y | p.eval₂ φ y = 0 ∧ ∀ j ∈ s, ∑ i, φ (a j.succ i) * y i =
    (b j).eval₂ φ x + if j = h then v else 0}

theorem slice_eq (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (h : Fin n) (v : ℝ) :
    {y : Fin n → ℝ | p.eval₂ φ y = 0 ∧ ∀ j ∈ s, ∑ i, φ (a j.succ i) * y i =
      (FlatAffineShiftedLevels.levels b h j).eval₂ φ (FlatAffineShiftedLevels.point x v)} = slice φ p s a b x h v := by
  simp only [slice, FlatAffineShiftedLevels.eval]

theorem exists_joined_stage_root (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (h : Fin n) (hs : h ∈ s) (v : ℝ)
    (hcompact : IsCompact (slice φ p s a b x h v))
    (hregular : ∀ y ∈ slice φ p s a b x h v, Function.Surjective (derivative φ p s a y))
    (hindependent : ¬∃ c : s → ℝ, ∀ i, φ (a 0 i) = ∑ j : s, c j * φ (a j.val.succ i))
    (z : Fin n → ℝ) (hz : z ∈ slice φ p s a b x h v) :
    ∃ (y : Fin n → ℝ) (mu : Fin (n + 1) → ℝ), mu 0 ≠ 0 ∧
      JoinedIn (slice φ p s a b x h v) z y ∧
      ∀ j, (row p s a b j).eval₂ φ (Sum.elim x (Sum.elim y mu)) =
        if j = Sum.inr h.succ then v else 0 := by
  have HE := slice_eq φ p s a b x h v
  obtain ⟨y, mu, hmu, hj, hr⟩ := FlatAffineComponentSampling.exists_joined_stage_root φ p s a
    (FlatAffineShiftedLevels.levels b h) (FlatAffineShiftedLevels.point x v)
    (HE.symm ▸ hcompact) (fun y hp hl => hregular y (HE ▸ ⟨hp, hl⟩)) hindependent z hz.1
    (fun j hj => by rw [FlatAffineShiftedLevels.eval]; exact hz.2 j hj)
  refine ⟨y, mu, hmu, HE ▸ hj, ?_⟩
  intro j
  have HV := FlatAffineShiftedLevels.row_eval φ p s a b h hs x (Sum.elim y mu) v j
  exact sub_eq_zero.mp (HV.symm.trans (hr j))

end LeanCanny.Geometry.FlatAffineShiftedComponentSampling
