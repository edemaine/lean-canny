/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.RadiusCriticalSource
public import LeanCanny.Geometry.RegularRadius

/-! # Regular compact perturbations of the encoded ETR source

For every fixed epsilon, all sufficiently small positive radii are regular for
every active set. Satisfiability is equivalent to nonemptiness throughout such
a regular interval. This proves existence, without an effective radius bound.
-/

@[expose] public section

namespace LeanCanny.ETR.RegularRadiusSource
open Geometry

theorem exists_regular_interval (bits : List Bool) (epsilon : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      ∀ (s : Finset (PerturbedSource.Index bits)) (z : PerturbedSource.Point bits),
        z ∈ PerturbedSource.feasible bits epsilon delta →
        (∀ i ∈ s, PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon z i = 0) →
        Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap
          (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s delta) z) := by
  obtain ⟨d, hd, hr⟩ := PolynomialPerturbation.exists_regular_interval (CompactSource.polynomial bits) epsilon
  exact ⟨d, hd, fun delta hp hs s z hz ha => hr delta hp hs s z ha hz.2⟩

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      (PerturbedSource.feasible bits epsilon delta).Nonempty ∧
        ∀ (s : Finset (PerturbedSource.Index bits)) (z : PerturbedSource.Point bits),
          z ∈ PerturbedSource.feasible bits epsilon delta →
          (∀ i ∈ s, PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon z i = 0) →
          Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap
            (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s delta) z) := by
  rw [PerturbedSource.correct]
  constructor
  · rintro ⟨epsilon, he, d, hd, hn⟩
    obtain ⟨r, hr, hregular⟩ := exists_regular_interval bits epsilon
    refine ⟨epsilon, he, min d r, lt_min hd hr, ?_⟩
    intro delta hp hs
    exact ⟨hn delta hp (lt_of_lt_of_le hs (min_le_left _ _)),
      hregular delta hp (lt_of_lt_of_le hs (min_le_right _ _))⟩
  · rintro ⟨epsilon, he, d, hd, h⟩
    exact ⟨epsilon, he, d, hd, fun delta hp hs => (h delta hp hs).1⟩

end LeanCanny.ETR.RegularRadiusSource
