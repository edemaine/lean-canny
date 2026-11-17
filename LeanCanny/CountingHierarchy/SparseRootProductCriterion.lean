/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SparseIntegerRootLabels
public import LeanCanny.CountingHierarchy.RootLabelProductCriterion

/-! # A bounded integer-label spectral-product criterion for real roots -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

@[expose] noncomputable def shiftedIntegerLabel (D e : ℕ) (L : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.C (-4 * (D : ℤ)) * L + Polynomial.C (e : ℤ)

theorem shiftedIntegerLabel_map_real (D e : ℕ) (L : Polynomial ℤ) :
    (shiftedIntegerLabel D e L).map (Int.castRingHom ℝ) =
      shiftedLabelPolynomial D e (L.map (Int.castRingHom ℝ)) := by
  simp only [shiftedIntegerLabel, shiftedLabelPolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Int.coe_castRingHom, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast]

/-- The complete integer label construction, including its short witness
 bound, reduces a real-root cutoff question to one spectral-product sign. -/
theorem root_below_iff_negative_sparse_product {D : ℕ} (p : Polynomial ℤ) (hp : p ≠ 0)
    (hD : 1 ≤ D) (hdeg : p.natDegree ≤ D) (N b : ℕ) (hDN : D ≤ 2 ^ N) (R : ℤ)
    (hpm : coefficientMass p ≤ 2 ^ b)
    (hb₀m : coefficientMass (Polynomial.C R - Polynomial.X) ≤ 2 ^ b) :
    (∃ x : ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 ∧ x < R) ↔
      ∃ L : List (Fin D × SignType), L.length ≤ N ∧ ∃ e : ℕ, e ≤ D ∧
        (∏ z ∈ complexRootSet (p.map (Int.castRingHom ℝ)), Polynomial.aeval z
          ((shiftedIntegerLabel D e (sparseIntegerRootLabel p (Polynomial.C R - Polynomial.X) N b L)).map
            (Int.castRingHom ℝ))).re < 0 := by
  let q := p.map (Int.castRingHom ℝ)
  let b₀ : Polynomial ℤ := Polynomial.C R - Polynomial.X
  let Label := {L : List (Fin D × SignType) // L.length ≤ N}
  let labels (a : Label) : Polynomial ℝ :=
    (sparseIntegerRootLabel p b₀ N b a.val).map (Int.castRingHom ℝ)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hqdeg : q.natDegree ≤ D := Polynomial.natDegree_map_le.trans hdeg
  have hb₀deg : b₀.natDegree ≤ D :=
    (Polynomial.natDegree_sub_le _ _).trans (by simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X,
      Nat.zero_max] using hD)
  have hb₀eval (x : ℝ) : b₀.eval₂ (Int.castRingHom ℝ) x = (R : ℝ) - x := by
    simp only [b₀, Polynomial.eval₂_sub, Polynomial.eval₂_C, Int.coe_castRingHom, Polynomial.eval₂_X]
  have hmargin (a : Label) (x : ℝ) (hx : q.eval x = 0) :
      (1 : ℝ) / 2 ≤ (labels a).eval x ∨ (labels a).eval x ≤ -(1 : ℝ) / 2 := by
    have hx' : p.eval₂ (Int.castRingHom ℝ) x = 0 := by simpa only [q, Polynomial.eval_map] using hx
    simpa only [labels, Polynomial.eval_map] using
      (sparseIntegerRootLabel_margin p b₀ hp N b a.val hdeg hb₀deg hpm hb₀m x hx').1
  have hsound (a : Label) (x : ℝ) (hx : q.eval x = 0) (hpos : 0 < (labels a).eval x) : x < R := by
    have hx' : p.eval₂ (Int.castRingHom ℝ) x = 0 := by simpa only [q, Polynomial.eval_map] using hx
    have hpos' : 0 < (sparseIntegerRootLabel p b₀ N b a.val).eval₂ (Int.castRingHom ℝ) x := by
      simpa only [labels, Polynomial.eval_map] using hpos
    have h := (sparseIntegerRootLabel_pos_iff p b₀ hp N b a.val a.property hdeg hb₀deg hpm hb₀m x hx').mp hpos'
    rw [hb₀eval] at h
    linarith [h.1]
  have hselect (hex : ∃ x : ℝ, q.eval x = 0 ∧ x < R) :
      ∃ a : Label, ∃ x : ℝ, q.eval x = 0 ∧ 0 < (labels a).eval x ∧
        ∀ y : ℝ, q.eval y = 0 → y ≠ x → (labels a).eval y < 0 := by
    have hx₀ : ∃ x : ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 ∧ 0 < b₀.eval₂ (Int.castRingHom ℝ) x := by
      obtain ⟨x, hx, hxR⟩ := hex
      refine ⟨x, by simpa only [q, Polynomial.eval_map] using hx, ?_⟩
      rw [hb₀eval]
      linarith
    obtain ⟨L, hL, x, hx, hpos, hother⟩ :=
      exists_sparseIntegerRootLabel p b₀ hp N b hdeg hDN hb₀deg hpm hb₀m hx₀
    refine ⟨⟨L, hL⟩, x, ?_, ?_, ?_⟩
    · simpa only [q, Polynomial.eval_map] using hx
    · simpa only [labels, Polynomial.eval_map] using hpos
    · intro y hy hne
      simpa only [labels, Polynomial.eval_map] using
        hother y (by simpa only [q, Polynomial.eval_map] using hy) hne
  have hcrit := root_below_iff_negative_label_product q hq D hD hqdeg (R : ℝ) labels hmargin hsound hselect
  constructor
  · intro hx
    obtain ⟨⟨L, hL⟩, e, he, hprod⟩ := hcrit.mp (by simpa only [q, Polynomial.eval_map] using hx)
    refine ⟨L, hL, e, he, ?_⟩
    simpa only [shiftedIntegerLabel_map_real, labels, q, b₀] using hprod
  · rintro ⟨L, hL, e, he, hprod⟩
    have hh : ∃ x : ℝ, q.eval x = 0 ∧ x < R := by
      apply hcrit.mpr
      refine ⟨⟨L, hL⟩, e, he, ?_⟩
      simpa only [shiftedIntegerLabel_map_real, labels, q, b₀] using hprod
    simpa only [q, Polynomial.eval_map] using hh

end LeanCanny.CountingHierarchy
