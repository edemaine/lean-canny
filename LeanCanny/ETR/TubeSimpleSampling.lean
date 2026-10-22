/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeSamplingRegular
public import LeanCanny.ETR.TubeJacobianFiniteSigns
public import LeanCanny.Computation.PSPACEBoolean

/-! # Exact polynomial-space testing for nonsingular compiled tube samples

The regular equations, inactive inequalities, original coordinate annihilants,
and a positive or negative actual native Jacobian determinant are tested
internally. Simple-root persistence covers every original at the selected
sample. No finiteness assumption on the other components is required.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSimpleSampling
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeNativeAnnihilator
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCharacteristicQuotient.regularSystem

variable (S : Source)

noncomputable def jacobian (c : List Bool) (w : TubeRegularSource.Variable (S.input c) → ℝ) : ℝ :=
  (TubeRegularJacobianBudget.polynomial (S.input c)
    (activeSet (TubeIndexed.arity (S.input c)) (S.mask c))).eval₂ (Int.castRingHom ℝ) w

noncomputable def source (sgn : SignType) : FiniteLeafSignBits.Source (TubeNativeFiniteSigns.arity S.packet) :=
  (TubeNativeFiniteSigns.source S.packet S.mask).append
    (TubeJacobianFiniteSigns.source S.input S.mask sgn)

noncomputable def access (sgn : SignType) : (source S sgn).Access :=
  (TubeNativeFiniteSigns.access S.packet S.mask S.packet_FP S.mask_FP).append
    (TubeJacobianFiniteSigns.access S.input S.mask sgn (mem_FP_comp S.packet_FP pairFst_mem_FP) S.mask_FP)

noncomputable def signedLanguage (sgn : SignType) : Language :=
  FiniteLeafSignBits.finiteSignLanguage S.family (TubeNativeFiniteSigns.arity S.packet) (source S sgn)

noncomputable def language : Language := signedLanguage S .pos ∪ signedLanguage S .neg

theorem allSigns_iff (sgn : SignType) (c : List Bool)
    (z : Fin (TubeNativeFiniteSigns.arity S.packet c) → ℝ) :
    (∀ j : Fin ((source S sgn).count c), SignType.sign (((source S sgn).polynomial c j.val).eval₂
      (Int.castRingHom ℝ) z) = (source S sgn).pattern c j.val) ↔
    TubeNativeFiniteSigns.satisfies S.packet S.mask c z ∧
      SignType.sign (jacobian S c (fun i => z (TubeHomogenization.outputEquiv (S.input c) i))) = sgn := by
  have H := FiniteLeafSignBits.Source.append_all_iff
    (TubeNativeFiniteSigns.source S.packet S.mask) (TubeJacobianFiniteSigns.source S.input S.mask sgn) c
    (fun p s => SignType.sign (p.eval₂ (Int.castRingHom ℝ) z) = s)
  exact H.trans (and_congr (TubeNativeFiniteSigns.allSigns_iff S.packet S.mask c z)
    (TubeJacobianFiniteSigns.allSigns_iff S.input S.mask sgn c z))

theorem signedLanguage_iff_native (sgn : SignType) (c : List Bool) : c ∈ signedLanguage S sgn ↔
    ∃ w : TubeRegularSource.Variable (S.input c) → ℝ,
      (∀ i, (S.polynomial (pair c (BinaryNatCode.encode
        (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂ (Int.castRingHom ℝ) (w i) = 0) ∧
      TubeNativeSampling.NativeSample S c w ∧ SignType.sign (jacobian S c w) = sgn := by
  constructor
  · rintro ⟨z, hz, hs⟩
    obtain ⟨hn, hj⟩ := (allSigns_iff S sgn c z).mp hs
    exact ⟨fun i => z (TubeHomogenization.outputEquiv (S.input c) i), fun i => hz _, hn, hj⟩
  · rintro ⟨w, hw, hn, hj⟩
    let z : Fin (TubeNativeFiniteSigns.arity S.packet c) → ℝ :=
      fun i => w ((TubeHomogenization.outputEquiv (S.input c)).symm i)
    refine ⟨z, ?_, (allSigns_iff S sgn c z).mpr ?_⟩
    · intro i
      simpa only [z, Equiv.apply_symm_apply, Source.family] using hw ((TubeHomogenization.outputEquiv (S.input c)).symm i)
    · change TubeNativeSampling.NativeSample S c (fun i => w ((TubeHomogenization.outputEquiv (S.input c)).symm
        (TubeHomogenization.outputEquiv (S.input c) i))) ∧ _
      simpa only [z, Equiv.symm_apply_apply] using And.intro hn hj

theorem signedLanguage_mem_PSPACE (sgn : SignType) : signedLanguage S sgn ∈ PSPACE := by
  obtain ⟨b, hb, hle⟩ := S.massExponent_binary.finiteEnvelope S.count_unary
  apply FiniteLeafSignBits.finiteSignLanguage_mem_PSPACE_from_residues S.family
    (TubeNativeFiniteSigns.arity S.packet) S.degreeBound b
    (fun c i _ => S.polynomial_ne_zero _)
    (fun c i _ => by simpa only [pairFst_pair, Source.family] using S.polynomial_degree (pair c (BinaryNatCode.encode i)))
    (fun c i hi => (S.polynomial_mass _).trans (Nat.pow_le_pow_right (by decide) (hle c i hi)))
    (source S sgn) (access S sgn)
    (TubeRegularFiniteSigns.arity_unary _ (mem_FP_comp S.packet_FP pairFst_mem_FP))
    S.degreeBound_binary hb S.coefficientEvaluator

theorem language_mem_PSPACE : language S ∈ PSPACE :=
  mem_PSPACE_union (signedLanguage_mem_PSPACE S .pos) (signedLanguage_mem_PSPACE S .neg)

private theorem sign_nonzero_iff (x : ℝ) : (SignType.sign x = .pos ∨ SignType.sign x = .neg) ↔ x ≠ 0 := by
  constructor
  · rintro (h | h) hx <;> rw [hx, sign_zero] at h <;> cases h
  · intro hx
    rcases lt_or_gt_of_ne hx with hn | hp
    · exact Or.inr (sign_eq_neg_one_iff.mpr hn)
    · exact Or.inl (sign_eq_one_iff.mpr hp)

theorem language_iff_native (c : List Bool) : c ∈ language S ↔
    ∃ w : TubeRegularSource.Variable (S.input c) → ℝ,
      (∀ i, (S.polynomial (pair c (BinaryNatCode.encode
        (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂ (Int.castRingHom ℝ) (w i) = 0) ∧
      TubeNativeSampling.NativeSample S c w ∧ jacobian S c w ≠ 0 := by
  change (c ∈ signedLanguage S .pos ∨ c ∈ signedLanguage S .neg) ↔ _
  rw [signedLanguage_iff_native, signedLanguage_iff_native]
  constructor
  · rintro (⟨w, hw, hn, hj⟩ | ⟨w, hw, hn, hj⟩)
    · exact ⟨w, hw, hn, (sign_nonzero_iff _).mp (Or.inl hj)⟩
    · exact ⟨w, hw, hn, (sign_nonzero_iff _).mp (Or.inr hj)⟩
  · rintro ⟨w, hw, hn, hj⟩
    rcases (sign_nonzero_iff _).mpr hj with hp | hm
    · exact Or.inl ⟨w, hw, hn, hp⟩
    · exact Or.inr ⟨w, hw, hn, hm⟩

/-- The pin argument preserves the entire native assignment when extracting
its compiled sample, including the value of the Jacobian determinant. -/
theorem compiled_of_native (c : List Bool) (w : TubeRegularSource.Variable (S.input c) → ℝ)
    (hw : ∀ i, (S.polynomial (pair c (BinaryNatCode.encode
      (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂ (Int.castRingHom ℝ) (w i) = 0)
    (hn : TubeNativeSampling.NativeSample S c w) :
    ∃ z, TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧
      S.decoded c z = w := by
  let x := TubeNativeSampleGeometry.spatial (S.packet c) w
  have hext : w = TubeNativeSampleGeometry.extend (S.packet c) (S.level c) x :=
    TubeNativeSampleGeometry.eq_extend_of_pins (S.packet c) (S.level c) w
      (fun i => S.parameters_pinned c w hw (.inl i))
      (fun p => S.parameters_pinned c w hw (.inr p))
  let z := TubeCompiledAffineRoots.compiledPoint (S.input c) (S.projection c) x
  refine ⟨z, ?_, ?_⟩
  · apply (TubeNativeSampleGeometry.compiledSample_iff (S.packet c) (S.mask c) (S.projection c)
      (S.level c) x).mpr
    exact ⟨by simpa only [← hext] using hn.1, hn.2⟩
  · have hd : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
        (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
      funext i
      rcases i with _ | ((i | i) | p) <;> rfl
    rw [hd]
    dsimp only [z]
    rw [TubeCompiledAffineRoots.decodedPoint_compiledPoint]
    exact hext.symm

/-- This predicate uses the actual native integer singularity polynomial. -/
noncomputable def SimpleSample (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) : Prop :=
  TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧
    jacobian S c (S.decoded c z) ≠ 0

/-- Native determinant nonsingularity is exactly the analytic chart condition. -/
theorem simple_iff_jacobian_ne_zero (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) :
    S.Simple c z ↔ jacobian S c (S.decoded c z) ≠ 0 := by
  have he : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
      (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
    funext i
    rcases i with _ | ((i | i) | p) <;> rfl
  have H := TubeRegularJacobianChart.packet_isInvertible_iff
    (S.packet c) (S.mask c) (S.projection c) (S.level c) z
  simpa only [Source.Simple, jacobian, ← he] using H

theorem simpleSample_iff (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) :
    SimpleSample S c z ↔ TubeLevelPacket.CompiledSample
      (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧ S.Simple c z :=
  and_congr Iff.rfl (simple_iff_jacobian_ne_zero S c z).symm

theorem simple_of_jacobian_ne_zero (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hdet : jacobian S c (S.decoded c z) ≠ 0) : S.Simple c z := by
  apply TubeRegularJacobianChart.packet_isInvertible (S.packet c) (S.mask c) (S.projection c) (S.level c) z
  have he : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
      (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
    funext i
    rcases i with _ | ((i | i) | p) <;> rfl
  simpa only [jacobian, ← he] using hdet

theorem sample_of_mem (c : List Bool) (h : c ∈ language S) : ∃ z, SimpleSample S c z := by
  obtain ⟨w, hw, hn, hJ⟩ := (language_iff_native S c).mp h
  obtain ⟨z, hz, hd⟩ := compiled_of_native S c w hw hn
  exact ⟨z, hz, by simpa only [hd] using hJ⟩

/-- Persistence of this one nonsingular root covers all original coordinates;
other components of the same fiber may be infinite. -/
theorem mem_of_sample (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) (hz : SimpleSample S c z) :
    c ∈ language S := by
  obtain ⟨hroot, hJ⟩ := hz
  have hs : S.Simple c z := simple_of_jacobian_ne_zero S c z hJ
  apply (language_iff_native S c).mpr
  refine ⟨S.decoded c z, S.polynomial_eval_decoded_of_regular c z hroot.1 hs, ?_, hJ⟩
  constructor
  · have he : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
        (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
      funext i
      rcases i with _ | ((i | i) | p) <;> rfl
    rw [he]
    exact TubeNativeSampleGeometry.regular_of_compiled (S.packet c) (S.mask c) (S.projection c)
      (S.level c) z hroot.1
  · exact hroot.2

theorem language_iff_compiled (c : List Bool) :
    c ∈ language S ↔ ∃ z, SimpleSample S c z :=
  ⟨sample_of_mem S c, fun ⟨z, hz⟩ => mem_of_sample S c z hz⟩

/-- An unconditional PSPACE decision theorem for existence of a compiled sample
whose actual native Jacobian determinant is nonzero. -/
theorem simpleSampleLanguage_mem_PSPACE : {c | ∃ z, SimpleSample S c z} ∈ PSPACE := by
  have he : {c | ∃ z, SimpleSample S c z} = language S := by
    ext c
    exact (language_iff_compiled S c).symm
  rw [he]
  exact language_mem_PSPACE S

/-- The same exact sampler recognizes the analytic simple-root condition. -/
theorem language_iff_simple (c : List Bool) : c ∈ language S ↔
    ∃ z, TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧ S.Simple c z :=
  (language_iff_compiled S c).trans (exists_congr fun z => simpleSample_iff S c z)

theorem compiledSimpleSampleLanguage_mem_PSPACE :
    {c | ∃ z, TubeLevelPacket.CompiledSample
      (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧ S.Simple c z} ∈ PSPACE := by
  have he : {c | ∃ z, TubeLevelPacket.CompiledSample
      (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧ S.Simple c z} = language S := by
    ext c
    exact (language_iff_simple S c).symm
  rw [he]
  exact language_mem_PSPACE S

/-- Concrete packet-and-mask input, using the zero projection and the internally
computed dyadic level. No coefficient reader or FP control is supplied. -/
noncomputable def universalLanguage : Language := language TubeNativeSampling.universalSource

theorem universalLanguage_mem_PSPACE : universalLanguage ∈ PSPACE :=
  language_mem_PSPACE TubeNativeSampling.universalSource

theorem universalLanguage_iff_compiled (q : List Bool) :
    q ∈ universalLanguage ↔ ∃ z, SimpleSample TubeNativeSampling.universalSource q z :=
  language_iff_compiled TubeNativeSampling.universalSource q

theorem universalLanguage_iff_simple (q : List Bool) : q ∈ universalLanguage ↔
    ∃ z, TubeLevelPacket.CompiledSample
      (pairFst q) (pairSnd q) (fun _ => 0) (TubeNativeSampling.universalSource.level q) z ∧
        TubeNativeSampling.universalSource.Simple q z :=
  language_iff_simple TubeNativeSampling.universalSource q

end LeanCanny.ETR.TubeSimpleSampling
