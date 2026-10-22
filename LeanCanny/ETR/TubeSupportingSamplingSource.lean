/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCriticalSamplingSource
public import LeanCanny.Geometry.TubeSupportingSampling

/-! # Unconditional semantic correctness of encoded tube projection sampling

Compact supporting projections remove the finite-critical-direction hypothesis
from existence of eventual projection samples. Directions and roots are real
witnesses. Finite, effective sampling and parameter choices are not established.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSupportingSamplingSource
open Geometry

theorem correct_eventual_projection_samples (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      ∃ v : TubeSource.Coordinate bits → ℝ,
        v (TubePolynomial.base (Fin (CompactSource.term bits).arity)) = 1 ∧
          TubePolynomial.EventualProjectionSamples (CompactSource.polynomial bits) epsilon delta v := by
  constructor
  · intro h
    obtain ⟨epsilon, he, d, hd, hn⟩ := (PerturbedSource.correct bits).mp h
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    have hsample := TubePolynomial.exists_eventual_projection_samples_of_feasible (CompactSource.polynomial bits)
      epsilon delta he.le hp (hn delta hp hs)
    exact hsample
  · rintro ⟨epsilon, he, d, hd, hs⟩
    apply TubeCriticalSamplingSource.of_eventual_projection_samples bits
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hr
    obtain ⟨v, _, hv⟩ := hs delta hp hr
    exact ⟨v, hv⟩

theorem correct_small_projection_samples (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.SmallProjectionSamples (CompactSource.polynomial bits) epsilon delta := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, hn⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    have hcorrect := TubePolynomial.nonempty_iff_small_projection_samples (CompactSource.polynomial bits)
      epsilon delta he.le hp
    exact hcorrect.mp (hn delta hp hs)
  · rintro ⟨epsilon, he, d, hd, hs⟩
    exact ⟨epsilon, he, d, hd, fun delta hp hr =>
      TubeFeasibilitySource.feasible_of_small_projection_samples bits epsilon delta he.le hp.le (hs delta hp hr)⟩

end LeanCanny.ETR.TubeSupportingSamplingSource
