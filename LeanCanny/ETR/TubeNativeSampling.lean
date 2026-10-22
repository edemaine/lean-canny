/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeAnnihilatorRoots
public import LeanCanny.ETR.TubeNativeFiniteSigns
public import LeanCanny.ETR.TubeNativeSampleGeometry
public import LeanCanny.Computation.FiniteBinaryEnvelope

/-! # A polynomial-space test for actual compiled tube samples

The original coordinate annihilants and rational pins are constructed from the
packet. Regular equations remove spurious root tuples. With finite complex
fibers, the resulting language is exactly existence of a compiled sample at
the internally selected dyadic level.
-/

@[expose] public section
namespace LeanCanny.ETR.TubeNativeSampling
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeNativeAnnihilator
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
set_option backward.isDefEq.respectTransparency false

variable (S : Source)

noncomputable def language : Language := TubeNativeFiniteSigns.language S.packet S.mask S.family

noncomputable def NativeSample (c : List Bool) (w : TubeRegularSource.Variable (S.input c) → ℝ) : Prop :=
  (∀ j, (TubeRegularSource.polynomial (S.input c)
    (activeSet (TubeIndexed.arity (S.input c)) (S.mask c)) j).eval₂ (Int.castRingHom ℝ) w = 0) ∧
  ∀ i, i ∉ activeSet (TubeIndexed.arity (S.input c)) (S.mask c) →
    0 < PolynomialPerturbation.parameterMap (CompactSource.polynomial (S.input c))
      (TubeLevelPacket.epsilon (S.packet c) : ℝ)
        (TubePolynomial.splitPoint (fun i => w (some (.inl (.inl i))))) i

theorem language_iff_native (c : List Bool) : c ∈ language S ↔
    ∃ w : TubeRegularSource.Variable (S.input c) → ℝ,
      (∀ i, (S.polynomial (pair c (BinaryNatCode.encode
        (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂ (Int.castRingHom ℝ) (w i) = 0) ∧
      NativeSample S c w := by
  rw [language, TubeNativeFiniteSigns.language_iff]
  constructor
  · rintro ⟨z, hz, hs⟩
    exact ⟨fun i => z (TubeHomogenization.outputEquiv (S.input c) i), fun i => hz _, hs⟩
  · rintro ⟨w, hw, hs⟩
    let z : Fin (TubeNativeFiniteSigns.arity S.packet c) → ℝ :=
      fun i => w ((TubeHomogenization.outputEquiv (S.input c)).symm i)
    refine ⟨z, ?_, ?_⟩
    · intro i
      simpa only [z, Equiv.apply_symm_apply, Source.family] using hw ((TubeHomogenization.outputEquiv (S.input c)).symm i)
    · change NativeSample S c (fun i => w ((TubeHomogenization.outputEquiv (S.input c)).symm
        (TubeHomogenization.outputEquiv (S.input c) i)))
      simpa only [Equiv.symm_apply_apply] using hs

/-- Every accepted tuple gives a true sample; this direction needs no fiber promise. -/
theorem sample_of_mem (c : List Bool) (h : c ∈ language S) :
    ∃ z, TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z := by
  obtain ⟨w, hw, he, hi⟩ := (language_iff_native S c).mp h
  have hext : w = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
      (TubeNativeSampleGeometry.spatial (S.packet c) w) :=
    TubeNativeSampleGeometry.eq_extend_of_pins (S.packet c) (S.level c) w
      (fun i => S.parameters_pinned c w hw (.inl i))
      (fun p => S.parameters_pinned c w hw (.inr p))
  refine ⟨TubeCompiledAffineRoots.compiledPoint (S.input c) (S.projection c)
    (TubeNativeSampleGeometry.spatial (S.packet c) w), ?_⟩
  apply (TubeNativeSampleGeometry.compiledSample_iff (S.packet c) (S.mask c) (S.projection c)
    (S.level c) _).mpr
  constructor
  · simpa only [← hext] using he
  · exact hi

/-- Finite compiled fibers ensure the computed coordinate annihilants cover
all samples, including singular solutions. -/
theorem mem_of_sample (c : List Bool)
    (hf : TubeLevelPacket.FiniteCompiledFibers.{0} (S.packet c) (S.level c))
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z) :
    c ∈ language S := by
  apply (language_iff_native S c).mpr
  refine ⟨S.decoded c z, S.polynomial_eval_decoded c hf z hz.1, ?_, hz.2⟩
  have he : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
      (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
    funext i
    rcases i with _ | ((i | i) | p) <;> rfl
  rw [he]
  exact TubeNativeSampleGeometry.regular_of_compiled (S.packet c) (S.mask c) (S.projection c)
    (S.level c) z hz.1

theorem language_iff_compiled (c : List Bool)
    (hf : TubeLevelPacket.FiniteCompiledFibers.{0} (S.packet c) (S.level c)) :
    c ∈ language S ↔ ∃ z, TubeLevelPacket.CompiledSample
      (S.packet c) (S.mask c) (S.projection c) (S.level c) z :=
  ⟨sample_of_mem S c, fun ⟨z, hz⟩ => mem_of_sample S c hf z hz⟩

/-- All univariate residues, degrees, nonzero proofs, and mass bounds are
internal. The input source supplies only polynomial-time packet and direction readers. -/
theorem language_mem_PSPACE : language S ∈ PSPACE := by
  obtain ⟨b, hb, hle⟩ := S.massExponent_binary.finiteEnvelope S.count_unary
  apply TubeNativeFiniteSigns.language_mem_PSPACE_from_residues S.packet S.mask S.family
    S.degreeBound b
    (fun c i _ => S.polynomial_ne_zero _)
    (fun c i _ => by simpa only [pairFst_pair, Source.family] using S.polynomial_degree (pair c (BinaryNatCode.encode i)))
    (fun c i hi => (S.polynomial_mass _).trans (Nat.pow_le_pow_right (by decide) (hle c i hi)))
    S.packet_FP S.mask_FP S.degreeBound_binary hb S.coefficientEvaluator

/-- A direct decision theorem for true samples, with finiteness used only
for the mathematical equivalence, never as a computational oracle. -/
theorem compiledSampleLanguage_mem_PSPACE
    (hf : ∀ c, TubeLevelPacket.FiniteCompiledFibers.{0} (S.packet c) (S.level c)) :
    {c | ∃ z, TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z} ∈ PSPACE := by
  have he : {c | ∃ z, TubeLevelPacket.CompiledSample
      (S.packet c) (S.mask c) (S.projection c) (S.level c) z} = language S := by
    ext c
    exact (language_iff_compiled S c (hf c)).symm
  rw [he]
  exact language_mem_PSPACE S

/-- The universal sampler input stores just a packet and an active mask.
The added projection is zero; all spatial coordinates still receive their
own reprojected annihilants. -/
noncomputable def universalSource : Source where
  packet := pairFst
  mask := pairSnd
  read _ := (Codec.integer 0).toBits
  projection _ _ := 0
  packet_FP := pairFst_mem_FP
  mask_FP := pairSnd_mem_FP
  read_FP := constFn_mem_FP _
  read_eq _ _ := rfl

noncomputable def universalLanguage : Language := language universalSource

theorem universalLanguage_mem_PSPACE : universalLanguage ∈ PSPACE :=
  language_mem_PSPACE universalSource

theorem universal_sample_of_mem (q : List Bool) (h : q ∈ universalLanguage) :
    ∃ z, TubeLevelPacket.CompiledSample (pairFst q) (pairSnd q) (fun _ => 0)
      (universalSource.level q) z := sample_of_mem universalSource q h

end LeanCanny.ETR.TubeNativeSampling
