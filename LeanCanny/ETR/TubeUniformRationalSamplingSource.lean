/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRationalSamplingSource
public import LeanCanny.Geometry.TubeUniformRationalSampling

/-! # Encoded ETR correctness with a uniform rational projection direction

At each admissible epsilon and delta, one rational direction and one active
set work throughout a small positive tube-level interval. All active root
sets are finite, and the selected one contains positive-inactive samples.
This is a qualitative criterion, without an effective search or space bound.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeUniformRationalSamplingSource
open Geometry

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.UniformRationalFiniteProjectionSamples (CompactSource.polynomial bits) epsilon delta := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, hn⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    have h := TubePolynomial.uniform_rational_finite_samples_of_feasible (CompactSource.polynomial bits)
      epsilon delta he.le hp (hn delta hp hs)
    exact h
  · rintro ⟨epsilon, he, d, hd, hs⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hr
    have h := TubePolynomial.nonempty_iff_uniform_rational_finite_samples (CompactSource.polynomial bits)
      epsilon delta he.le hp
    exact h.mpr (hs delta hp hr)

end LeanCanny.ETR.TubeUniformRationalSamplingSource
