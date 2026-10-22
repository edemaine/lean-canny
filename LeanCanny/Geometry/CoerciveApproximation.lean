/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoercivePolynomialSampling

/-! # Polynomial roots and bounded approximate critical samples

A root in a fixed penalty sublevel is equivalent to arbitrarily small positive
regularizations having critical points in that sublevel with linearly small
squared residual. This formulation uses only one perturbation parameter.
-/

@[expose] public section

namespace LeanCanny.Geometry.CoerciveApproximation
open scoped Classical Topology
open Filter Set MvPolynomial
open CoercivePolynomialSampling
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def Sample (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (B s : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, eval x (pderiv i (regularization q D s)) = 0) ∧
    penalty D x ≤ B ∧ (eval x q) ^ 2 ≤ s * B

theorem root_of_samples (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (B : ℝ)
    (s : ℕ → ℝ) (hs0 : Tendsto s atTop (𝓝 0))
    (h : ∀ k, ∃ x, penalty D x ≤ B ∧ (eval x q) ^ 2 ≤ s k * B) :
    ∃ a, eval a q = 0 ∧ penalty D a ≤ B := by
  choose x hx hr using h
  obtain ⟨a, ha, φ, hφ, ht⟩ := (isCompact_sublevel (n := n) D B).tendsto_subseq hx
  have hq : Tendsto (fun k => (eval (x (φ k)) q) ^ 2) atTop (𝓝 ((eval a q) ^ 2)) :=
    ((MvPolynomial.continuous_eval q).continuousAt.tendsto.comp ht).pow 2
  have hz : Tendsto (fun k => s (φ k) * B) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using (hs0.comp hφ.tendsto_atTop).mul_const B
  have hle : (eval a q) ^ 2 ≤ 0 := le_of_tendsto_of_tendsto hq hz
    (Eventually.of_forall fun k => hr (φ k))
  exact ⟨a, sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)), ha⟩

theorem root_iff_samples (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (B : ℝ) :
    (∃ a, eval a q = 0 ∧ penalty D a ≤ B) ↔
      ∀ s : ℝ, 0 < s → ∃ x, Sample q D B s x := by
  constructor
  · rintro ⟨a, ha, hB⟩ s hs
    obtain ⟨x, _hm, hc, hp, hr⟩ := exists_critical_minimizer q D a ha s hs
    exact ⟨x, hc, hp.trans hB, hr.trans (mul_le_mul_of_nonneg_left hB hs.le)⟩
  · intro h
    apply root_of_samples q D B (fun k => 1 / ((k : ℝ) + 1))
      tendsto_one_div_add_atTop_nhds_zero_nat
    intro k
    obtain ⟨x, _hc, hp, hr⟩ := h (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨x, hp, hr⟩

/-- An eventual interval suffices; no regularity of the chosen samples is
needed for the compactness converse. -/
theorem root_iff_eventually_samples (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (B : ℝ) :
    (∃ a, eval a q = 0 ∧ penalty D a ≤ B) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → ∃ x, Sample q D B s x := by
  constructor
  · intro h
    exact ⟨1, zero_lt_one, fun s hs _ => (root_iff_samples q D B).mp h s hs⟩
  · rintro ⟨δ, hδ, h⟩
    let s : ℕ → ℝ := fun k => δ / 2 * (1 / ((k : ℝ) + 1))
    have hs0 : Tendsto s atTop (𝓝 0) := by
      simpa only [s, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2)
    apply root_of_samples q D B s hs0
    intro k
    have hs : 0 < s k := by dsimp [s]; positivity
    have hsδ : s k < δ := by
      have hd : 1 / ((k : ℝ) + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith [(show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
      have hle : s k ≤ δ / 2 := by
        dsimp [s]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ δ / 2)
      linarith
    obtain ⟨x, _hc, hp, hr⟩ := h (s k) hs hsδ
    exact ⟨x, hp, hr⟩

end LeanCanny.Geometry.CoerciveApproximation
