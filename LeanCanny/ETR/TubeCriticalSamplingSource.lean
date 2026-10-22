/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeFeasibilitySource
public import LeanCanny.Geometry.TubeCriticalSampling

/-! # Encoded ETR projection sampling under finite-critical-direction hypotheses

The reverse implication is unconditional. The forward implication uses the
explicit hypothesis that normalized directions with finite active critical
sets exist throughout a small-radius interval. One direction and one active
set then work for every sufficiently small tube level. Generic existence and
effective selection of these directions, and finite tube sampling, remain open.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCriticalSamplingSource
open Geometry

theorem of_eventual_projection_samples (bits : List Bool)
    (h : ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      ∃ v : TubeSource.Coordinate bits → ℝ,
        TubePolynomial.EventualProjectionSamples (CompactSource.polynomial bits) epsilon delta v) :
    bits ∈ ETR.language := by
  apply TubeFeasibilitySource.of_projection_samples bits
  obtain ⟨epsilon, he, d, hd, hs⟩ := h
  refine ⟨epsilon, he, d, hd, ?_⟩
  intro delta hp hr
  obtain ⟨v, hv⟩ := hs delta hp hr
  exact TubePolynomial.small_projection_samples_of_eventual (CompactSource.polynomial bits) epsilon delta v hv

theorem correct_given_finite_critical_directions (bits : List Bool)
    (hfinite : ∀ epsilon : ℝ, 0 < epsilon → ∃ r : ℝ, 0 < r ∧ ∀ delta : ℝ, 0 < delta → delta < r →
      TubePolynomial.HasFiniteCriticalDirection (CompactSource.polynomial bits) epsilon delta) :
    bits ∈ ETR.language ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
        ∃ v : TubeSource.Coordinate bits → ℝ,
          v (TubePolynomial.base (Fin (CompactSource.term bits).arity)) = 1 ∧
            TubePolynomial.FiniteActiveCriticalSets (CompactSource.polynomial bits) epsilon delta v ∧
            TubePolynomial.EventualProjectionSamples (CompactSource.polynomial bits) epsilon delta v := by
  constructor
  · intro h
    obtain ⟨epsilon, he, d, hd, hn⟩ := (PerturbedSource.correct bits).mp h
    obtain ⟨r, hr, hregular⟩ := TubePolynomial.exists_regular_active_interval (CompactSource.polynomial bits) epsilon
    obtain ⟨q, hq, hfin⟩ := hfinite epsilon he
    refine ⟨epsilon, he, min d (min r q), lt_min hd (lt_min hr hq), ?_⟩
    intro delta hp hs
    have hd' : delta < d := lt_of_lt_of_le hs (min_le_left _ _)
    have hrq : delta < min r q := lt_of_lt_of_le hs (min_le_right _ _)
    have hr' : delta < r := lt_of_lt_of_le hrq (min_le_left _ _)
    have hq' : delta < q := lt_of_lt_of_le hrq (min_le_right _ _)
    have hsample := TubePolynomial.exists_eventual_projection_samples (CompactSource.polynomial bits) epsilon delta
      he.le hp (hn delta hp hd') (hregular delta hp hr') (hfin delta hp hq')
    exact hsample
  · rintro ⟨epsilon, he, d, hd, hs⟩
    apply of_eventual_projection_samples bits
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hr
    obtain ⟨v, _, _, hv⟩ := hs delta hp hr
    exact ⟨v, hv⟩

end LeanCanny.ETR.TubeCriticalSamplingSource
