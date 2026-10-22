/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSign

/-! # Lowest parameter coefficients annihilate limits of polynomial roots

The outer variable is the perturbation parameter; each integer polynomial
coefficient is a polynomial in the sampled coordinate. Removing the lowest
parameter power before taking limits preserves a nonzero annihilator.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialLimitAnnihilator
open Polynomial Filter
open scoped Topology

noncomputable def value (p : Polynomial (Polynomial ℤ)) (s t : ℝ) : ℝ :=
  p.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) s

theorem continuous_value (p : Polynomial (Polynomial ℤ)) :
    Continuous (fun z : ℝ × ℝ => value p z.1 z.2) := by
  unfold value
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply continuous_finsetSum
  intro i _
  exact (((p.coeff i).continuous_eval₂ (Int.castRingHom ℝ)).comp continuous_snd).mul
    (continuous_fst.pow i)

theorem trailingCoeff_eval_eq_zero (p : Polynomial (Polynomial ℤ))
    (s t : ℕ → ℝ) (a : ℝ)
    (hs : ∀ k, s k ≠ 0) (hs0 : Tendsto s atTop (𝓝 0))
    (ht : Tendsto t atTop (𝓝 a)) (hz : ∀ k, value p (s k) (t k) = 0) :
    p.trailingCoeff.eval₂ (Int.castRingHom ℝ) a = 0 := by
  obtain ⟨q, hq, hq0⟩ := LeanCanny.Algebra.InfinitesimalSign.factor_at_trailingDegree p
  have hvanish (k : ℕ) : value q (s k) (t k) = 0 := by
    have h := hz k
    unfold value at h ⊢
    rw [hq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hs k))
  have hlim := (continuous_value q).continuousAt.tendsto.comp (hs0.prodMk_nhds ht)
  have he : value q 0 a = 0 := tendsto_nhds_unique hlim
    (show Tendsto (fun k => value q (s k) (t k)) atTop (𝓝 0) from by
      simpa only [hvanish] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  simpa only [value, Polynomial.eval₂_at_zero, hq0, Polynomial.coe_eval₂RingHom] using he

end LeanCanny.Geometry.PolynomialLimitAnnihilator
