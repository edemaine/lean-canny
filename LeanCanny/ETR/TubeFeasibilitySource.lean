/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeConvergenceSource
public import LeanCanny.Geometry.TubeProjectionFeasibility

/-! # Correctness of tube feasibility for encoded ETR

ETR satisfiability is equivalent to eventual positive-inactive tube samples,
and to arbitrarily small weak-inactive tube samples. Arbitrarily small integer
projection roots cannot produce false positives. The forward restriction to
finite critical samples still requires the generic-direction argument.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeFeasibilitySource
open Geometry

theorem feasible_of_small_samples (bits : List Bool) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta)
    (h : TubePolynomial.SmallSamples (CompactSource.polynomial bits) epsilon delta) :
    (PerturbedSource.feasible bits epsilon delta).Nonempty :=
  TubePolynomial.feasible_of_small_samples (CompactSource.polynomial bits) epsilon delta he hd h

theorem feasible_of_small_projection_samples (bits : List Bool) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta)
    (h : TubePolynomial.SmallProjectionSamples (CompactSource.polynomial bits) epsilon delta) :
    (PerturbedSource.feasible bits epsilon delta).Nonempty :=
  TubePolynomial.feasible_of_small_projection_samples (CompactSource.polynomial bits) epsilon delta he hd h

theorem correct_small_samples (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.SmallSamples (CompactSource.polynomial bits) epsilon delta := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, h⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    exact (TubePolynomial.nonempty_iff_small_samples (CompactSource.polynomial bits) epsilon delta he.le hp).mp (h delta hp hs)
  · rintro ⟨epsilon, he, d, hd, h⟩
    exact ⟨epsilon, he, d, hd, fun delta hp hs => feasible_of_small_samples bits epsilon delta he.le hp.le (h delta hp hs)⟩

theorem correct_eventual_positive_samples (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.EventualPositiveSamples (CompactSource.polynomial bits) epsilon delta := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, h⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    exact TubePolynomial.eventual_positive_samples_of_feasible (CompactSource.polynomial bits) epsilon delta hp (h delta hp hs)
  · rintro ⟨epsilon, he, d, hd, h⟩
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    exact (TubePolynomial.nonempty_iff_eventual_positive_samples (CompactSource.polynomial bits) epsilon delta he.le hp).mpr (h delta hp hs)

theorem of_projection_samples (bits : List Bool)
    (h : ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      TubePolynomial.SmallProjectionSamples (CompactSource.polynomial bits) epsilon delta) : bits ∈ ETR.language := by
  apply (PerturbedSource.correct bits).mpr
  obtain ⟨epsilon, he, d, hd, h⟩ := h
  exact ⟨epsilon, he, d, hd, fun delta hp hs => feasible_of_small_projection_samples bits epsilon delta he.le hp.le (h delta hp hs)⟩

end LeanCanny.ETR.TubeFeasibilitySource
