/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoordinateCriticalLimits

/-! # One coordinate-candidate grid covers every relatively clopen zero piece -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial Filter Set LeanCanny.Algebra
open scoped Topology Classical

variable {n : ℕ}

theorem candidateCoordinates_meet_clopen (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D)
    (C : Set (Geometry.CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ)))) (hC : IsClopen C)
    (x₀ : Geometry.CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ))) (hx₀ : x₀ ∈ C) :
    ∃ a : Geometry.CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ)), a ∈ C ∧
      ∀ i, (candidateCoordinate q D hD i).eval₂ (Int.castRingHom ℝ) (a.val i) = 0 := by
  let d := 2 * (D + 1)
  have hd : 1 ≤ d := by dsimp only [d]; omega
  have hF : (q ^ 2).totalDegree ≤ d + 1 := (totalDegree_pow q 2).trans (by dsimp only [d]; nlinarith)
  let s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let u : ℕ → ℝ := fun k => ((k : ℝ) + 1) / ((2 * (D + 1) + 2 : ℕ) : ℝ)
  have hs (k) : 0 < s k := by dsimp only [s]; positivity
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  have hu : Tendsto u atTop atTop := hnat.atTop_div_const (by positivity)
  obtain ⟨y, a, phi, ha, hphi, hlim, _, hcrit⟩ := Geometry.UnboundedCoerciveComponents.exists_critical_limits
    (q.map (Int.castRingHom ℝ)) (D + 1) C hC x₀ hx₀ s hs hs0
  refine ⟨a, ha, fun i => ?_⟩
  let P := Bivariate.swap (parametricCoordinatePolynomial d (q ^ 2) hF i)
  apply leadingCoefficient_root_of_filtered_limit P (u ∘ phi) (fun k => y (phi k) i) (a.val i)
    (hu.comp hphi.tendsto_atTop) ((continuous_apply i).continuousAt.tendsto.comp hlim)
  filter_upwards [hcrit] with k hk
  dsimp only [P]
  rw [integer_bivariate_swap_eval]
  have heq : (s (phi k) * ((2 * (D + 1) + 2 : ℕ) : ℝ))⁻¹ = u (phi k) := by
    simp only [s, u, mul_inv_rev, inv_inv, div_eq_mul_inv]
    ring
  have hc := criticalLower_of_coercive_gradient (q.map (Int.castRingHom ℝ)) (D + 1)
    (s (phi k)) (hs _) (y (phi k)) hk
  rw [heq] at hc
  have hc' : ∀ j, MvPolynomial.aeval (y (phi k))
      (criticalLower (d + 1) (fun _ => 0) (u (phi k)) ((q ^ 2).map (Int.castRingHom ℝ)) j) =
        y (phi k) j ^ (d + 1) := by
    simpa only [d, map_pow] using hc
  have h := parametricCoordinatePolynomial_root d hd (q ^ 2) hF i (u (phi k)) (y (phi k)) hc'
  simpa only [Polynomial.eval_map, parameterEvaluation, Function.comp_apply] using h

end LeanCanny.CountingHierarchy
