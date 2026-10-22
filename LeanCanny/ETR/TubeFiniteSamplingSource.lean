/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeSupportingSamplingSource
public import LeanCanny.Geometry.TubeFiniteSampling

/-! # Encoded ETR correctness of qualitative finite tube sampling

Satisfiability is equivalent to eventual finite projection root sets containing
positive-inactive samples. One active set works throughout each small-level
interval; the normalized real direction may depend on the level. Effective
direction search, root enumeration, and parameter bounds remain separate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeFiniteSamplingSource
open Geometry

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.EventualFiniteProjectionSamples (CompactSource.polynomial bits) epsilon delta := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, hn⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    have h := TubePolynomial.eventual_finite_samples_of_feasible (CompactSource.polynomial bits)
      epsilon delta he.le hp (hn delta hp hs)
    exact h
  · rintro ⟨epsilon, he, d, hd, hs⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hr
    have h := TubePolynomial.small_projection_samples_of_eventual_finite (CompactSource.polynomial bits)
      epsilon delta (hs delta hp hr)
    exact TubeFeasibilitySource.feasible_of_small_projection_samples bits epsilon delta he.le hp.le h

end LeanCanny.ETR.TubeFiniteSamplingSource
