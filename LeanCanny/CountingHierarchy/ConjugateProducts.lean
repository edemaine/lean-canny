/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Signs of products over conjugation-stable finite sets -/

public section

namespace LeanCanny.CountingHierarchy

open Complex
open scoped ComplexConjugate BigOperators Classical

/-- A product over nonreal conjugate pairs is a nonnegative real number.
The argument also allows test values to vanish. -/
theorem nonreal_conjugate_product_nonneg (S : Finset ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, f (conj z) = conj (f z))
    (hreal : ∀ z ∈ S, z.im ≠ 0) (hconj : ∀ z ∈ S, conj z ∈ S) :
    ∃ r : ℝ, 0 ≤ r ∧ (∏ z ∈ S, f z) = (r : ℂ) := by
  revert hreal hconj
  refine Finset.strongInductionOn S ?_
  intro S ih hreal hconj
  by_cases hS : S.Nonempty
  · obtain ⟨z, hz⟩ := hS
    have hcz := hconj z hz
    have hne : conj z ≠ z := by
      intro he
      exact hreal z hz (Complex.conj_eq_iff_im.mp he)
    let T := (S.erase z).erase (conj z)
    have hsub : T ⊆ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hproper : T ⊂ S :=
      (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset hz)
    have hcT (w : ℂ) (hw : w ∈ T) : conj w ∈ T := by
      have hw' := Finset.mem_erase.mp hw
      have hw'' := Finset.mem_erase.mp hw'.2
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        apply hw''.1
        exact (starRingEnd ℂ).injective he
      · apply Finset.mem_erase.mpr
        constructor
        · intro he
          apply hw'.1
          have hh := congrArg conj he
          simpa only [Complex.conj_conj] using hh
        · exact hconj w (hsub hw)
    obtain ⟨r, hr, hp⟩ := ih T hproper (fun w hw => hreal w (hsub hw)) hcT
    refine ⟨‖f z‖ ^ 2 * r, mul_nonneg (sq_nonneg _) hr, ?_⟩
    have hcz' : conj z ∈ S.erase z := Finset.mem_erase.mpr ⟨hne, hcz⟩
    rw [← Finset.mul_prod_erase S f hz, ← Finset.mul_prod_erase (S.erase z) f hcz']
    change f z * (f (conj z) * ∏ w ∈ T, f w) = _
    rw [hf, hp, ← mul_assoc, Complex.mul_conj']
    push_cast
    rfl
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    exact ⟨1, by positivity, by simp⟩

/-- Avoiding zero test values makes the conjugate-pair contribution positive. -/
theorem nonreal_conjugate_product_pos (S : Finset ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, f (conj z) = conj (f z))
    (hreal : ∀ z ∈ S, z.im ≠ 0) (hconj : ∀ z ∈ S, conj z ∈ S)
    (hnz : ∀ z ∈ S, f z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (∏ z ∈ S, f z) = (r : ℂ) := by
  obtain ⟨r, hr, he⟩ := nonreal_conjugate_product_nonneg S f hf hreal hconj
  refine ⟨r, lt_of_le_of_ne hr ?_, he⟩
  intro hz
  have hp : (∏ z ∈ S, f z) ≠ 0 := Finset.prod_ne_zero_iff.mpr hnz
  apply hp
  rw [he, ← hz, Complex.ofReal_zero]

/-- The real-root contribution determines the sign once the nonreal
 conjugate contribution is known to be positive. -/
theorem conjugate_product_factorization (S : Finset ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, f (conj z) = conj (f z)) (hconj : ∀ z ∈ S, conj z ∈ S) :
    ∃ r : ℝ, 0 ≤ r ∧
      ((∀ z ∈ S, z.im ≠ 0 → f z ≠ 0) → 0 < r) ∧
      (∏ z ∈ S, f z) = ((∏ z ∈ S.filter (fun z => z.im = 0), (f z).re) * r : ℝ) := by
  let N := S.filter (fun z => z.im ≠ 0)
  have hcN (z : ℂ) (hz : z ∈ N) : conj z ∈ N := by
    have hh := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    exact ⟨hconj z hh.1, by simpa only [Complex.conj_im, neg_ne_zero] using hh.2⟩
  obtain ⟨r, hr, hp⟩ := nonreal_conjugate_product_nonneg N f hf
    (fun z hz => (Finset.mem_filter.mp hz).2) hcN
  refine ⟨r, hr, ?_, ?_⟩
  · intro hnz
    have hn : (∏ z ∈ N, f z) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun z hz => hnz z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
    apply lt_of_le_of_ne hr
    intro he
    apply hn
    rw [hp, ← he, Complex.ofReal_zero]
  · have hreal : (∏ z ∈ S.filter (fun z => z.im = 0), f z) =
        ((∏ z ∈ S.filter (fun z => z.im = 0), (f z).re) : ℝ) := by
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      have hfix : conj (f z) = f z := by rw [← hf, Complex.conj_eq_iff_im.mpr hz']
      have him := Complex.conj_eq_iff_im.mp hfix
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using him
    have he := (Finset.prod_filter_mul_prod_filter_not S (fun z => z.im = 0) f).symm
    rw [hreal, hp] at he
    simpa only [Complex.ofReal_mul] using he

/-- A negative conjugate-stable product requires a negative real factor. -/
theorem exists_negative_real_factor_of_product_neg (S : Finset ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, f (conj z) = conj (f z)) (hconj : ∀ z ∈ S, conj z ∈ S)
    (hneg : (∏ z ∈ S, f z).re < 0) :
    ∃ z ∈ S, z.im = 0 ∧ (f z).re < 0 := by
  obtain ⟨r, hr, _hpos, he⟩ := conjugate_product_factorization S f hf hconj
  by_contra! hnot
  have hprod : 0 ≤ ∏ z ∈ S.filter (fun z => z.im = 0), (f z).re :=
    Finset.prod_nonneg (fun z hz => hnot z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
  rw [he, Complex.ofReal_re] at hneg
  exact (not_lt_of_ge (mul_nonneg hprod hr)) hneg

/-- One negative real factor, positive remaining real factors and nonzero
 nonreal factors give a strictly negative product. -/
theorem conjugate_product_neg_of_unique_negative_real_factor
    (S : Finset ℂ) (f : ℂ → ℂ) (hf : ∀ z, f (conj z) = conj (f z))
    (hconj : ∀ z ∈ S, conj z ∈ S) (z₀ : ℂ) (hz₀ : z₀ ∈ S) (him₀ : z₀.im = 0)
    (hneg : (f z₀).re < 0)
    (hpos : ∀ z ∈ S, z.im = 0 → z ≠ z₀ → 0 < (f z).re)
    (hnz : ∀ z ∈ S, z.im ≠ 0 → f z ≠ 0) : (∏ z ∈ S, f z).re < 0 := by
  obtain ⟨r, _hr, hrpos, he⟩ := conjugate_product_factorization S f hf hconj
  let R := S.filter (fun z => z.im = 0)
  have hmem : z₀ ∈ R := Finset.mem_filter.mpr ⟨hz₀, him₀⟩
  have hprod : 0 < ∏ z ∈ R.erase z₀, (f z).re := by
    apply Finset.prod_pos
    intro z hz
    have hh := Finset.mem_erase.mp hz
    have hz' := Finset.mem_filter.mp hh.2
    exact hpos z hz'.1 hz'.2 hh.1
  have hreal : (∏ z ∈ R, (f z).re) < 0 := by
    rw [← Finset.mul_prod_erase R (fun z => (f z).re) hmem]
    exact mul_neg_of_neg_of_pos hneg hprod
  rw [he, Complex.ofReal_re]
  exact mul_neg_of_neg_of_pos hreal (hrpos hnz)

end LeanCanny.CountingHierarchy
