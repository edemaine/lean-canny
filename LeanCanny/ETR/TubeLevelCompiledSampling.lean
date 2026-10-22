/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelRootLift
public import LeanCanny.ETR.TubeLevelSamplingSource

/-! # ETR correctness in terms of actual compiled affine samples

One stored rational packet and active mask work throughout a positive level
interval. Every added linear projection admits compiled roots preserving the
positive inactive signs. The affine fibers are finite over every real
extension. This is a qualitative equivalence; no size bound or search
algorithm for the packet, mask, or interval is asserted.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
universe uL
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

def FiniteCompiledFibers (c : List Bool) (alpha : ℝ) : Prop :=
  ∀ (L : Type uL) [Field L] [Algebra ℝ L],
    ∀ (active : List Bool → List Bool) (ell : List Bool → ℕ → ℤ),
      (MvPolynomial.zeroLocus L (ProjectiveNullstellensatz.generated
        (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator ell c
          (algebraMap ℝ L alpha)))).Finite

noncomputable def CompiledSample (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) : Prop :=
  (∀ i, MvPolynomial.eval z
    (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c alpha i) = 0) ∧
    ∀ i, i ∉ activeSet (TubeIndexed.arity (pairFst c)) mask →
      0 < PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst c)) (epsilon c : ℝ)
        (TubePolynomial.splitPoint (samplePoint c z)) i

noncomputable def UniformCompiledSamples (bits : List Bool) (eps del : ℚ) : Prop :=
  ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
    direction c (TubePolynomial.base _) = 1 ∧
    ∃ mask : List Bool, ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      FiniteCompiledFibers.{uL} c alpha ∧
        ∀ ell : ℕ → ℤ, ∃ z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ,
          CompiledSample c mask ell alpha z

theorem uniform_compiled_samples_of_packet_samples (bits : List Bool) (eps del : ℚ)
    (h : UniformPacketSamples.{uL} bits eps del) : UniformCompiledSamples.{uL} bits eps del := by
  obtain ⟨c, hc, he, hd, hb, s, a, ha, hs⟩ := h
  subst bits
  subst eps
  subst del
  obtain ⟨b, hbp, hlift⟩ := exists_compiled_lift_interval c hb
  let mask := activeCode (TubeIndexed.arity (pairFst c)) s
  have hmask : activeSet (TubeIndexed.arity (pairFst c)) mask = s :=
    TubeEncoding.activeSet_activeCode (TubeIndexed.arity (pairFst c)) s
  refine ⟨c, rfl, rfl, rfl, hb, mask, min a b, lt_min ha hbp, ?_⟩
  intro alpha hp hl
  obtain ⟨hf, x, hx, hi⟩ := hs alpha hp (hl.trans_le (min_le_left _ _))
  refine ⟨hf, ?_⟩
  intro ell
  have hx' : x ∈ TubePolynomial.projectionRootSet (CompactSource.polynomial (pairFst c))
      (activeSet (TubeIndexed.arity (pairFst c)) mask)
      (epsilon c : ℝ) (delta c : ℝ) alpha (fun i => (direction c i : ℝ)) := by
    simpa only [hmask, direction] using hx
  obtain ⟨z, hz, hxz⟩ := hlift alpha hp (hl.trans_le (min_le_right _ _)) (fun _ => mask) ell x hx'
  refine ⟨z, hz, ?_⟩
  rw [hxz]
  dsimp +instances only [TubeIndexed.arity, PerturbedSource.Index, TubeEncoding.Constraint] at *
  intro i hnot
  apply hi i
  simpa only [hmask] using hnot

theorem packet_samples_of_uniform_compiled_samples (bits : List Bool) (eps del : ℚ)
    (h : UniformCompiledSamples.{uL} bits eps del) : UniformPacketSamples.{uL} bits eps del := by
  obtain ⟨c, hc, he, hd, hb, mask, a, ha, hs⟩ := h
  subst bits
  subst eps
  subst del
  refine ⟨c, rfl, rfl, rfl, hb, activeSet (TubeIndexed.arity (pairFst c)) mask, a, ha, ?_⟩
  intro alpha hp hl
  obtain ⟨hf, hsample⟩ := hs alpha hp hl
  obtain ⟨z, hz, hi⟩ := hsample (fun _ => 0)
  refine ⟨hf, samplePoint c z, ?_, hi⟩
  simpa only [direction] using projection_root_of_compiled (fun _ => mask) (fun _ => 0) c alpha z hz

theorem uniform_compiled_samples_iff (bits : List Bool) (eps del : ℚ) :
    UniformCompiledSamples.{uL} bits eps del ↔ UniformPacketSamples.{uL} bits eps del :=
  ⟨packet_samples_of_uniform_compiled_samples bits eps del,
    uniform_compiled_samples_of_packet_samples bits eps del⟩

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelSamplingSource
universe uL

theorem compiled_correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ eps : ℚ, 0 < eps ∧ ∀ del : ℚ, 0 < del → TubeLevelPacket.UniformCompiledSamples.{uL} bits eps del := by
  simpa only [TubeLevelPacket.uniform_compiled_samples_iff] using (correct.{uL} bits)

end LeanCanny.ETR.TubeLevelSamplingSource
