/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RealRootProducts

/-! # Root labels reduce a root-existence test to one spectral-product sign

This module proves the sign argument. The quantitative construction and
counting-hierarchy access certificates for the label polynomials are separate.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

@[expose] noncomputable def shiftedLabelPolynomial (D e : ℕ) (L : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (-4 * (D : ℝ)) * L + Polynomial.C (e : ℝ)

theorem shiftedLabelPolynomial_eval (D e : ℕ) (L : Polynomial ℝ) (x : ℝ) :
    (shiftedLabelPolynomial D e L).eval x = -4 * (D : ℝ) * L.eval x + e := by
  simp only [shiftedLabelPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

/-- Label soundness, sign margins and isolation imply the finite shifted
 spectral-product criterion. The shift range has only `D+1` possibilities. -/
theorem root_below_iff_negative_label_product {α : Type*}
    (p : Polynomial ℝ) (hp : p ≠ 0) (D : ℕ) (hD : 1 ≤ D) (hdeg : p.natDegree ≤ D)
    (R : ℝ) (L : α → Polynomial ℝ)
    (hmargin : ∀ a x, p.eval x = 0 → (1 : ℝ) / 2 ≤ (L a).eval x ∨ (L a).eval x ≤ -(1 : ℝ) / 2)
    (hsound : ∀ a x, p.eval x = 0 → 0 < (L a).eval x → x < R)
    (hselect : (∃ x : ℝ, p.eval x = 0 ∧ x < R) →
      ∃ a x, p.eval x = 0 ∧ 0 < (L a).eval x ∧
        ∀ y : ℝ, p.eval y = 0 → y ≠ x → (L a).eval y < 0) :
    (∃ x : ℝ, p.eval x = 0 ∧ x < R) ↔
      ∃ a e, e ≤ D ∧
        (∏ z ∈ complexRootSet p, Polynomial.aeval z (shiftedLabelPolynomial D e (L a))).re < 0 := by
  constructor
  · intro hroot
    obtain ⟨a, x, hx, hax, hother⟩ := hselect hroot
    let base := Polynomial.C (-4 * (D : ℝ)) * L a
    obtain ⟨e, he, hnz⟩ := exists_shift_nonzero_on_complex_roots p D hdeg base
    refine ⟨a, e, he, ?_⟩
    apply product_neg_of_unique_negative_real_root p _ hp x hx
    · rw [shiftedLabelPolynomial_eval]
      exact (shifted_factor_neg_iff D e hD he _ (hmargin a x hx)).mpr hax
    · intro y hy hne
      rw [shiftedLabelPolynomial_eval]
      have hmy : (L a).eval y ≤ -(1 : ℝ) / 2 := by
        rcases hmargin a y hy with hh | hh
        · have ho := hother y hy hne
          linarith
        · exact hh
      have hpos := shifted_factor_pos D e ((L a).eval y) hmy
      have hdpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
      linarith
    · intro z hz _him
      simpa only [shiftedLabelPolynomial, Polynomial.aeval_add, Polynomial.aeval_C,
        map_natCast, base] using hnz z hz
  · rintro ⟨a, e, he, hprod⟩
    obtain ⟨x, hx, hneg⟩ := exists_real_root_negative_of_product_neg p _ hp hprod
    rw [shiftedLabelPolynomial_eval] at hneg
    exact ⟨x, hx, hsound a x hx ((shifted_factor_neg_iff D e hD he _ (hmargin a x hx)).mp hneg)⟩

end LeanCanny.CountingHierarchy
