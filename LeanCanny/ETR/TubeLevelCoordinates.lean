/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteSystemTransfer
public import LeanCanny.Algebra.IntegerCoordinatePolynomials
public import LeanCanny.ETR.TubeFiniteSystemBaseChange
public import LeanCanny.ETR.TubeLevelCompiledSampling
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Integer rational coordinates for actual tube samples at rational levels

Finite compiled complex fibers yield rational univariate representations of
the actual rational-level system. Decoding is sound and complete over the
reals, with nonzero integer coordinate denominators at every parameter root.
The representation is existential: coefficient heights and construction space
are not bounded here.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

noncomputable def rationalSystem (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ) :
    Fin (TubeParameter.spatialCount (pairFst c)) →
      MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℚ :=
  TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator (fun _ => ell) c alpha

theorem eval_rationalSystem {E : Type*} [Field E] [Algebra ℚ E]
    (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → E)
    (j : Fin (TubeParameter.spatialCount (pairFst c))) :
    MvPolynomial.eval₂ (algebraMap ℚ E) z (rationalSystem c mask ell alpha j) =
      MvPolynomial.eval z (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask)
        numerator denominator (fun _ => ell) c (algebraMap ℚ E alpha) j) := by
  rw [← MvPolynomial.eval_map, rationalSystem, TubeCharacteristicQuotient.map_finiteSystem]

theorem finite_rationalSystem (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ)) :
    (FiniteSystemCoordinates.zeroSet (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)).Finite := by
  let f : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  apply FiniteSystemCoordinates.finite_zeroSet_of_embedding _ f
  have he : FiniteSystemCoordinates.zeroSet (L := ℂ) (rationalSystem c mask ell alpha) =
      MvPolynomial.zeroLocus ℂ (ProjectiveNullstellensatz.generated
        (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
          (fun _ => ell) c (algebraMap ℝ ℂ (alpha : ℝ)))) := by
    rw [ProjectiveNullstellensatz.zeroLocus_generated]
    ext z
    change (∀ j, MvPolynomial.eval₂ (algebraMap ℚ ℂ) z (rationalSystem c mask ell alpha j) = 0) ↔ _
    simp_rw [eval_rationalSystem]
    have hc : algebraMap ℚ ℂ alpha = algebraMap ℝ ℂ (alpha : ℝ) := by simp
    rw [hc]
    rfl
  rw [he]
  exact hf ℂ (fun _ => mask) (fun _ => ell)

theorem nonempty_integer_coordinates (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ)) :
    Nonempty (Σ r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ)
      (rationalSystem c mask ell alpha), IntegerCoordinatePolynomials.IntegerData r) := by
  obtain ⟨r⟩ := FiniteSystemCoordinates.nonempty_algebraicClosure_representation _
    (finite_rationalSystem c mask ell alpha hf)
  obtain ⟨d⟩ := IntegerCoordinatePolynomials.nonempty_integerData r
  exact ⟨⟨r, d⟩⟩

/-- Integer parameter roots and the full compiled real zero set are in bijection. -/
noncomputable def integerRootEquiv (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ))
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha))
    (d : IntegerCoordinatePolynomials.IntegerData r) :
    {θ : ℝ // Polynomial.aeval θ d.polynomial = 0} ≃
      FiniteSystemCoordinates.zeroSet (L := ℝ) (rationalSystem c mask ell alpha) :=
  d.rootEquiv.trans (r.rootEquivOfFinite (finite_rationalSystem c mask ell alpha hf))

noncomputable def inactiveSigns (c mask : List Bool)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) : Prop :=
  ∀ i, i ∉ activeSet (TubeIndexed.arity (pairFst c)) mask →
    0 < PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst c)) (epsilon c : ℝ)
      (TubePolynomial.splitPoint (samplePoint c z)) i

theorem compiledSample_iff_zeroSet (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) :
    CompiledSample c mask ell (alpha : ℝ) z ↔
      z ∈ FiniteSystemCoordinates.zeroSet (L := ℝ) (rationalSystem c mask ell alpha) ∧ inactiveSigns c mask z := by
  have hc : algebraMap ℚ ℝ alpha = (alpha : ℝ) := by simp
  unfold CompiledSample FiniteSystemCoordinates.zeroSet inactiveSigns
  simp only [Set.mem_ofPred_eq, eval_rationalSystem, hc]

/-- Only an integer univariate root and decoded inactive-sign tests remain. -/
theorem exists_compiledSample_iff_integer (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ))
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha))
    (d : IntegerCoordinatePolynomials.IntegerData r) :
    (∃ z, CompiledSample c mask ell (alpha : ℝ) z) ↔
      ∃ θ : ℝ, Polynomial.aeval θ d.polynomial = 0 ∧ inactiveSigns c mask (d.decode θ) := by
  simp_rw [compiledSample_iff_zeroSet]
  simpa only [d.root_iff, d.decode_eq] using
    r.exists_solution_iff (finite_rationalSystem c mask ell alpha hf) (inactiveSigns c mask)

noncomputable def UniformCoordinateSamples (bits : List Bool) (eps del : ℚ) : Prop :=
  ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
    direction c (TubePolynomial.base _) = 1 ∧ ∃ mask : List Bool, ∃ a : ℝ, 0 < a ∧
      ∀ alpha : ℚ, 0 < alpha → (alpha : ℝ) < a →
        FiniteCompiledFibers.{0} c (alpha : ℝ) ∧ ∀ ell : ℕ → ℤ,
          ∃ r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha),
            ∃ d : IntegerCoordinatePolynomials.IntegerData r,
              ∃ θ : ℝ, Polynomial.aeval θ d.polynomial = 0 ∧ inactiveSigns c mask (d.decode θ)

theorem uniform_coordinate_samples_of_compiled (bits : List Bool) (eps del : ℚ)
    (h : UniformCompiledSamples.{0} bits eps del) : UniformCoordinateSamples bits eps del := by
  obtain ⟨c, hc, he, hd, hb, mask, a, ha, hs⟩ := h
  refine ⟨c, hc, he, hd, hb, mask, a, ha, ?_⟩
  intro alpha hp hl
  have hpR : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast hp
  obtain ⟨hf, hr⟩ := hs (alpha : ℝ) hpR hl
  refine ⟨hf, ?_⟩
  intro ell
  obtain ⟨⟨r, d⟩⟩ := nonempty_integer_coordinates c mask ell alpha hf
  exact ⟨r, d, (exists_compiledSample_iff_integer c mask ell alpha hf r d).mp (hr ell)⟩

theorem feasible_of_uniform_coordinate_samples (bits : List Bool) (eps del : ℚ)
    (he : 0 ≤ eps) (hd : 0 < del) (h : UniformCoordinateSamples bits eps del) :
    (PolynomialPerturbation.perturbed (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ)).Nonempty := by
  obtain ⟨c, hc, hec, hdc, _hb, mask, a, ha, hs⟩ := h
  subst bits
  subst eps
  subst del
  apply TubePolynomial.feasible_of_small_projection_samples _ _ _
    (by exact_mod_cast he) (by exact_mod_cast hd.le)
  intro b hb
  obtain ⟨alpha, hp, hl⟩ := exists_rat_btwn (lt_min ha hb)
  have hpQ : (0 : ℚ) < alpha := by exact_mod_cast hp
  obtain ⟨hf, hr⟩ := hs alpha hpQ (hl.trans_le (min_le_left _ _))
  obtain ⟨r, d, θ, hθ, hi⟩ := hr (fun _ => 0)
  obtain ⟨z, hz⟩ := (exists_compiledSample_iff_integer c mask (fun _ => 0) alpha hf r d).mpr ⟨θ, hθ, hi⟩
  refine ⟨(alpha : ℝ), hp, hl.trans_le (min_le_right _ _),
    activeSet (TubeIndexed.arity (pairFst c)) mask, samplePoint c z,
    (fun i => (direction c i : ℝ)), ?_, ?_⟩
  · exact projection_root_of_compiled (fun _ => mask) (fun _ => 0) c (alpha : ℝ) z hz.1
  · exact fun i hnot => (hz.2 i hnot).le

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelSamplingSource
open Geometry

/-- An exact ETR criterion with integer univariate coordinate representations
at rational tube levels. No size or computation bound is claimed. -/
theorem coordinates_correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ eps : ℚ, 0 < eps ∧ ∀ del : ℚ, 0 < del → TubeLevelPacket.UniformCoordinateSamples bits eps del := by
  constructor
  · intro h
    obtain ⟨eps, he, hs⟩ := (compiled_correct.{0} bits).mp h
    exact ⟨eps, he, fun del hd => TubeLevelPacket.uniform_coordinate_samples_of_compiled bits eps del (hs del hd)⟩
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
        TubeLevelPacket.feasible_of_uniform_coordinate_samples bits eps del he.le hdQ (hs del hdQ)⟩
    rwa [PerturbedSource.unperturbed_eq] at hn

end LeanCanny.ETR.TubeLevelSamplingSource
