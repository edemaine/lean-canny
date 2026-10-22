/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelSampling

/-! # Encoded ETR correctness with stored rational tube parameters

A positive rational margin suffices. At every positive rational radius,
one stored rational packet preserves positive-inactive samples throughout a
small positive level interval and has finite compiled fibers over every
real extension field. These conditions are equivalent to ETR satisfiability
on all bitstrings. Bounds for choosing and searching the packets and levels
remain open.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelSamplingSource
open LeanCanny.Encoding Geometry
universe uL
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
theorem correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ eps : ℚ, 0 < eps ∧ ∀ del : ℚ, 0 < del → TubeLevelPacket.UniformPacketSamples.{uL} bits eps del := by
  constructor
  · intro h
    obtain ⟨epsilon, he, hn⟩ := (CompactSource.correct bits).mp h
    obtain ⟨eps, hp, hl⟩ := exists_rat_btwn he
    have hpQ : (0 : ℚ) < eps := by exact_mod_cast hp
    have hnQ : (PolynomialPerturbation.feasible (CompactSource.polynomial bits) (eps : ℝ)).Nonempty := by
      rw [PerturbedSource.unperturbed_eq]
      exact hn.mono (CompactSource.feasible_mono bits hl.le)
    refine ⟨eps, hpQ, ?_⟩
    intro del hd
    have hdR : (0 : ℝ) ≤ (del : ℝ) := by exact_mod_cast hd.le
    exact TubeLevelPacket.uniform_packet_samples_of_feasible bits eps del hpQ.le hd
      (PolynomialPerturbation.nonempty_of_feasible _ _ _ hdR hnQ)
  · rintro ⟨eps, he, hs⟩
    have heR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast he
    apply (CompactSource.correct bits).mpr
    refine ⟨(eps : ℝ), heR, ?_⟩
    have hn : (PolynomialPerturbation.feasible (CompactSource.polynomial bits) (eps : ℝ)).Nonempty := by
      apply PolynomialPerturbation.feasible_of_arbitrarily_small _ _ heR.le
      intro eta heta
      obtain ⟨del, hd, hde⟩ := exists_rat_btwn heta
      have hdQ : (0 : ℚ) < del := by exact_mod_cast hd
      exact ⟨(del : ℝ), hd, hde,
        TubeLevelPacket.feasible_of_uniform_packet_samples bits eps del he.le hdQ (hs del hdQ)⟩
    rwa [PerturbedSource.unperturbed_eq] at hn

end LeanCanny.ETR.TubeLevelSamplingSource
