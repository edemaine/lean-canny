/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeFiniteSamplingSource
public import LeanCanny.Geometry.TubeRationalSampling

/-! # Encoded ETR correctness of rational finite tube sampling

The rational direction witnesses give finite root sets containing suitable
positive-inactive samples. The witnesses may vary with the level, and their
bit-size and the small-parameter bounds remain qualitative.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRationalSamplingSource
open Geometry

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.EventualRationalFiniteProjectionSamples (CompactSource.polynomial bits) epsilon delta := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, hn⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    have h := TubePolynomial.eventual_rational_finite_samples_of_feasible (CompactSource.polynomial bits)
      epsilon delta he.le hp (hn delta hp hs)
    exact h
  · rintro ⟨epsilon, he, d, hd, hs⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hr
    have h := TubePolynomial.nonempty_iff_eventual_rational_finite_samples (CompactSource.polynomial bits)
      epsilon delta he.le hp
    exact h.mpr (hs delta hp hr)

end LeanCanny.ETR.TubeRationalSamplingSource
