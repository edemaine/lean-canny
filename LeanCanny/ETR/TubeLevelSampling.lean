/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelChoice
public import LeanCanny.Geometry.TubeUniformRationalSampling

/-! # Positive-inactive tube samples with one stored rational packet

A feasible perturbed source has one packet and one active set supplying
positive-inactive critical samples throughout a common small positive level
interval. The same packet has finite compiled affine fibers over every real
extension, for all active sets. Conversely, these samples imply feasibility.
The packet length and interval have no source-size bounds here.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open Set MvPolynomial
open scoped Classical Topology
universe uL
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

noncomputable def UniformPacketSamples (bits : List Bool) (eps del : ℚ) : Prop :=
  ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
    direction c (TubePolynomial.base _) = 1 ∧
    ∃ s : Finset (PerturbedSource.Index bits), ∃ a : ℝ, 0 < a ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < a →
        (∀ (L : Type uL) [Field L] [Algebra ℝ L],
          ∀ (active : List Bool → List Bool) (ell : List Bool → ℕ → ℤ),
            (zeroLocus L (ProjectiveNullstellensatz.generated
              (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator ell c (algebraMap ℝ L alpha)))).Finite) ∧
        ∃ x ∈ TubePolynomial.projectionRootSet (CompactSource.polynomial bits) s (eps : ℝ) (del : ℝ) alpha
            (fun i => (rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val : ℝ)),
          ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) (eps : ℝ)
            (TubePolynomial.splitPoint x) i

theorem uniform_packet_samples_of_feasible (bits : List Bool) (eps del : ℚ)
    (he : 0 ≤ eps) (hd : 0 < del)
    (hn : (PolynomialPerturbation.perturbed (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ)).Nonempty) :
    UniformPacketSamples.{uL} bits eps del := by
  have heR : (0 : ℝ) ≤ (eps : ℝ) := by exact_mod_cast he
  have hdR : (0 : ℝ) < (del : ℝ) := by exact_mod_cast hd
  obtain ⟨v, z, hz, hv, hstrict⟩ := TubePolynomial.exists_strict_supporting_maximum
    (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ) heR hdR.le hn
  obtain ⟨U, hU, a, ha, hsamples⟩ := TubePolynomial.exists_sample_neighborhood_of_strict
    (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ) v z hdR hz hstrict
  obtain ⟨c, hc, hce, hcd, hnear, hb, b, hbp, hf⟩ := exists_uniform_finite_packet.{uL} bits eps del v hv U hU
  subst bits
  have hbR : (fun i => (rationalValue c (pointEquiv (TubeIndexed.arity (pairFst c)) i).val : ℝ))
      (TubePolynomial.base _) = 1 := by
    change (direction c (TubePolynomial.base _) : ℝ) = 1
    exact_mod_cast hb
  refine ⟨c, rfl, hce, hcd, hb, PolynomialPerturbation.activeSet (CompactSource.polynomial (pairFst c)) (eps : ℝ) z,
    min a b, lt_min ha hbp, ?_⟩
  intro alpha hp hl
  exact ⟨hf alpha hp (hl.trans_le (min_le_right _ _)),
    hsamples alpha hp (hl.trans_le (min_le_left _ _)) _ hnear hbR⟩

theorem feasible_of_uniform_packet_samples (bits : List Bool) (eps del : ℚ)
    (he : 0 ≤ eps) (hd : 0 < del) (h : UniformPacketSamples.{uL} bits eps del) :
    (PolynomialPerturbation.perturbed (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ)).Nonempty := by
  obtain ⟨c, _, _, _, _, s, a, ha, hr⟩ := h
  have hs : TubePolynomial.EventualProjectionSamples (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ)
      (fun i => (rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val : ℝ)) :=
    ⟨s, a, ha, fun alpha hp hl => (hr alpha hp hl).2⟩
  apply TubePolynomial.feasible_of_small_projection_samples
    (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ)
  · exact_mod_cast he
  · exact_mod_cast hd.le
  · exact TubePolynomial.small_projection_samples_of_eventual _ _ _ _ hs

theorem nonempty_iff_uniform_packet_samples (bits : List Bool) (eps del : ℚ) (he : 0 ≤ eps) (hd : 0 < del) :
    (PolynomialPerturbation.perturbed (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ)).Nonempty ↔
      UniformPacketSamples.{uL} bits eps del :=
  ⟨uniform_packet_samples_of_feasible bits eps del he hd, feasible_of_uniform_packet_samples bits eps del he hd⟩
end LeanCanny.ETR.TubeLevelPacket
