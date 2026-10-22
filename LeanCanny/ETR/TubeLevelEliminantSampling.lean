/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelCompiledSampling
public import LeanCanny.ETR.TubeCharacteristicLowestSpecialization
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Nonzero lowest-coefficient eliminants covering the retained tube samples

Finiteness over the complex numbers makes every compiled real root annihilate
the lowest quotient coefficient. Its existing dyadic specialization bound
ensures this univariate polynomial is nonzero. For each linear projection,
shrinking the level interval preserves samples with positive inactive signs.
The packet and interval still have no bounds in the original source size.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

noncomputable def eliminant (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ) : Polynomial ℝ :=
  TubeCharacteristicQuotient.lowestProjectionPolynomial pairFst (fun _ => mask)
    numerator denominator (fun _ => ell) c alpha

noncomputable def projectionValue (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) : ℝ :=
  z (TubeCharacteristicQuotient.finiteParameterIndex (pairFst c))

theorem eliminant_eval_compiled_root (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (hf : FiniteCompiledFibers.{0} c alpha)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
        (fun _ => ell) c alpha i) = 0) :
    (eliminant c mask ell alpha).eval (projectionValue c z) = 0 := by
  have hroot : TubeCharacteristicQuotient.regularSystem pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c alpha (projectionValue c z, fun j => z j.succ) = 0 := by
    funext i
    have h := hz i
    rw [TubeCharacteristicQuotient.eval_finiteSystem] at h
    simp_rw [TubeCharacteristicQuotient.eval_finiteChartVariables] at h
    exact h
  exact TubeCharacteristicQuotient.lowestProjectionPolynomial_eval_eq_zero_of_finite_extension_fiber
    (L := ℂ) pairFst (fun _ => mask) numerator denominator (fun _ => ell) c alpha
    (hf ℂ (fun _ => mask) (fun _ => ell)) _ hroot

def projectionRead (ell : ℕ → ℤ) (q : List Bool) : List Bool :=
  (Codec.integer (ell (Nat.fromBitsLE (pairSnd q)))).toBits

theorem projectionRead_correct (ell : ℕ → ℤ) (c : List Bool) (i : ℕ) :
    projectionRead ell (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell i)).toBits := by
  simp only [projectionRead, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def eliminantThreshold (c : List Bool) (ell : ℕ → ℤ) : ℝ :=
  InfinitesimalSign.dyadic (Nat.fromBitsLE
    (TubeDeformation.specializationExponent pairFst (projectionRead ell) bounds.degree bounds.bits c))

theorem eliminantThreshold_pos (c : List Bool) (ell : ℕ → ℤ) : 0 < eliminantThreshold c ell :=
  InfinitesimalSign.dyadic_pos _

theorem eliminant_ne_zero_of_small (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (hp : 0 < alpha) (hsmall : alpha ≤ eliminantThreshold c ell) :
    eliminant c mask ell alpha ≠ 0 :=
  TubeCharacteristicQuotient.lowestProjectionPolynomial_ne_zero_of_small
    pairFst (fun _ => mask) numerator denominator (fun _ => ell) c (projectionRead ell) bounds
    (fun c i _ => projectionRead_correct ell c i) alpha hp hsmall

theorem eliminant_natDegree_le (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ) :
    (eliminant c mask ell alpha).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (pairFst c))
        (TubeCleared.matrixWidth (pairFst c)) :=
  TubeCharacteristicQuotient.lowestProjectionPolynomial_natDegree_le
    pairFst (fun _ => mask) numerator denominator (fun _ => ell) c alpha

noncomputable def projectionValues (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ) : Set ℝ :=
  {u | ∃ z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ,
    (∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
        (fun _ => ell) c alpha i) = 0) ∧ projectionValue c z = u}

theorem projectionValues_finite_and_ncard_le (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (hf : FiniteCompiledFibers.{0} c alpha) (hp : 0 < alpha)
    (hsmall : alpha ≤ eliminantThreshold c ell) :
    (projectionValues c mask ell alpha).Finite ∧
      (projectionValues c mask ell alpha).ncard ≤
        FixedWidthPolynomial.count (TubeParameter.spatialCount (pairFst c))
          (TubeCleared.matrixWidth (pairFst c)) := by
  have hne := eliminant_ne_zero_of_small c mask ell alpha hp hsmall
  have hsub : projectionValues c mask ell alpha ⊆ ((eliminant c mask ell alpha).roots.toFinset : Set ℝ) := by
    rintro u ⟨z, hz, rfl⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr
      (eliminant_eval_compiled_root c mask ell alpha hf z hz))
  refine ⟨(Finset.finite_toSet _).subset hsub, (Set.ncard_le_ncard hsub).trans ?_⟩
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (eliminant_natDegree_le c mask ell alpha))

noncomputable def UniformEliminantSamples (bits : List Bool) (eps del : ℚ) : Prop :=
  ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
    direction c (TubePolynomial.base _) = 1 ∧ ∃ mask : List Bool,
      ∀ ell : ℕ → ℤ, ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
        FiniteCompiledFibers.{0} c alpha ∧ eliminant c mask ell alpha ≠ 0 ∧
          ∃ z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ,
            CompiledSample c mask ell alpha z ∧
              (eliminant c mask ell alpha).eval (projectionValue c z) = 0

theorem uniform_eliminant_samples_of_compiled (bits : List Bool) (eps del : ℚ)
    (h : UniformCompiledSamples.{0} bits eps del) : UniformEliminantSamples bits eps del := by
  obtain ⟨c, hc, he, hd, hb, mask, a, ha, hs⟩ := h
  refine ⟨c, hc, he, hd, hb, mask, ?_⟩
  intro ell
  refine ⟨min a (eliminantThreshold c ell), lt_min ha (eliminantThreshold_pos c ell), ?_⟩
  intro alpha hp hl
  obtain ⟨hf, hr⟩ := hs alpha hp (hl.trans_le (min_le_left _ _))
  obtain ⟨z, hz⟩ := hr ell
  exact ⟨hf, eliminant_ne_zero_of_small c mask ell alpha hp (hl.trans_le (min_le_right _ _)).le,
    z, hz, eliminant_eval_compiled_root c mask ell alpha hf z hz.1⟩

theorem packet_samples_of_uniform_eliminant (bits : List Bool) (eps del : ℚ)
    (h : UniformEliminantSamples bits eps del) : UniformPacketSamples.{0} bits eps del := by
  obtain ⟨c, hc, he, hd, hb, mask, hs⟩ := h
  subst bits
  subst eps
  subst del
  obtain ⟨a, ha, hr⟩ := hs (fun _ => 0)
  refine ⟨c, rfl, rfl, rfl, hb, activeSet (TubeIndexed.arity (pairFst c)) mask, a, ha, ?_⟩
  intro alpha hp hl
  obtain ⟨hf, _, z, hz, _⟩ := hr alpha hp hl
  refine ⟨hf, samplePoint c z, ?_, hz.2⟩
  simpa only [direction] using projection_root_of_compiled (fun _ => mask) (fun _ => 0) c alpha z hz.1

theorem uniform_eliminant_samples_iff (bits : List Bool) (eps del : ℚ) :
    UniformEliminantSamples bits eps del ↔ UniformPacketSamples.{0} bits eps del :=
  ⟨packet_samples_of_uniform_eliminant bits eps del,
    fun h => uniform_eliminant_samples_of_compiled bits eps del
      (uniform_compiled_samples_of_packet_samples bits eps del h)⟩

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelSamplingSource

theorem eliminant_correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ eps : ℚ, 0 < eps ∧ ∀ del : ℚ, 0 < del → TubeLevelPacket.UniformEliminantSamples bits eps del := by
  simpa only [TubeLevelPacket.uniform_eliminant_samples_iff] using (correct.{0} bits)

end LeanCanny.ETR.TubeLevelSamplingSource
