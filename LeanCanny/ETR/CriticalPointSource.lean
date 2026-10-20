/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.RegularRadiusSource
public import LeanCanny.Geometry.PerturbedCriticalPoint

/-! # Critical projection maxima for encoded ETR

An ETR input is satisfiable exactly when sufficiently small regular compact
perturbations have critical maxima for every linear projection. The critical
point carries normalized multipliers on its active set and radius equation.
Finite sampling and an effective parameter selection remain separate steps.
-/

@[expose] public section

namespace LeanCanny.ETR.CriticalPointSource
open Geometry

noncomputable def activeSet (bits : List Bool) (epsilon : ℝ) (z : PerturbedSource.Point bits) :
    Finset (PerturbedSource.Index bits) :=
  PolynomialPerturbation.activeSet (CompactSource.polynomial bits) epsilon z

noncomputable def activeMap (bits : List Bool) (epsilon delta : ℝ) (s : Finset (PerturbedSource.Index bits)) :=
  ActiveRadius.fixedMap (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s delta

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d →
      ∀ L : PerturbedSource.Point bits →L[ℝ] ℝ,
        ∃ z ∈ PerturbedSource.feasible bits epsilon delta,
          IsMaxOn L (PerturbedSource.feasible bits epsilon delta) z ∧
            ∃ Λ : Module.Dual ℝ ((activeSet bits epsilon z → ℝ) × ℝ), ∀ h,
              L h = Λ (fderiv ℝ (activeMap bits epsilon delta (activeSet bits epsilon z)) z h) := by
  constructor
  · intro h
    obtain ⟨epsilon, he, d, hd, hregular⟩ := (RegularRadiusSource.correct bits).mp h
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs L
    obtain ⟨hn, hr⟩ := hregular delta hp hs
    exact PolynomialPerturbation.exists_critical_max (CompactSource.polynomial bits)
      epsilon delta he.le hp.le hn L hr
  · rintro ⟨epsilon, he, d, hd, h⟩
    apply (PerturbedSource.correct bits).mpr
    refine ⟨epsilon, he, d, hd, ?_⟩
    intro delta hp hs
    obtain ⟨z, hz, _⟩ := h delta hp hs 0
    exact ⟨z, hz⟩

end LeanCanny.ETR.CriticalPointSource
