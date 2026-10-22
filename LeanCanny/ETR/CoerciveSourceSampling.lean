/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoerciveRootRadius
public import LeanCanny.ETR.CompactSource
public import LeanCanny.ETR.PolynomialMass
public import LeanCanny.ETR.TermArityFP

/-! # Coercive critical sampling for every encoded ETR input

The verified equation compiler supplies an integer polynomial before rational
compactification. Its degree and coefficient mass are bounded by the normalized
source size. ETR membership is exactly eventual bounded critical sampling of
its coercive perturbation, including malformed-input defaults. The radius and
penalty exponents have polynomial binary lengths; no sampling algorithm is
asserted here.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveSourceSampling
open LeanCanny.Encoding
open LeanCanny.Algebra
open scoped BigOperators

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def dimension (bits : List Bool) : ℕ := (CompactSource.term bits).arity

/-- The original compiled equation, with exactly its finite coordinate arity. -/
noncomputable def polynomial (bits : List Bool) : MvPolynomial (Fin (dimension bits)) ℤ :=
  (CompactSource.term bits).finitePolynomial (dimension bits)

def degreeAllowance (bits : List Bool) : ℕ := CompactSource.size bits
def massAllowance (bits : List Bool) : ℕ := CompactSource.size bits

noncomputable def radiusExponent (bits : List Bool) : ℕ :=
  CoerciveRadiusBits.massExponent (dimension bits) (degreeAllowance bits) (massAllowance bits)
noncomputable def penaltyExponent (bits : List Bool) : ℕ :=
  CoerciveRadiusBits.penaltyExponent (dimension bits) (degreeAllowance bits) (massAllowance bits)

theorem dimension_unary : UnaryFn dimension :=
  TermArity.arity_unary RationalSubstitutionBits.compiledTerm_mem_FP

theorem degreeAllowance_unary : UnaryFn degreeAllowance := CompactSource.size_unary
theorem massAllowance_unary : UnaryFn massAllowance := CompactSource.size_unary

theorem dimension_le_size (bits : List Bool) : dimension bits ≤ CompactSource.size bits := by
  rw [CompactSource.size_eq]
  exact (CompactSource.term bits).arity_le_dataSize

theorem polynomial_degree (bits : List Bool) : (polynomial bits).totalDegree ≤ degreeAllowance bits := by
  exact ((CompactSource.term bits).totalDegree_finitePolynomial (dimension bits)).trans
    (by simpa only [degreeAllowance, CompactSource.size_eq] using
      (CompactSource.term bits).degreeBound_le_dataSize)

theorem polynomial_mass (bits : List Bool) : MvMass.mass (polynomial bits) ≤ 2 ^ massAllowance bits := by
  simpa only [polynomial, massAllowance, CompactSource.size_eq] using
    (CompactSource.term bits).finitePolynomial_mass (dimension bits)

theorem root_iff (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ x : Fin (dimension bits) → ℝ, (polynomial bits).eval₂ (Int.castRingHom ℝ) x = 0 := by
  rw [RationalSubstitutionBits.compiledTerm_correct]
  exact (CompactSource.term bits).exists_zero_iff_finitePolynomial

/-- An actual critical point, with bounded diagonal penalty and small squared
residual, using only the compiled source allowances. -/
def Sample (bits : List Bool) (s : ℝ) (x : Fin (dimension bits) → ℝ) : Prop :=
  Geometry.CoerciveApproximation.Sample ((polynomial bits).map (Int.castRingHom ℝ))
    (degreeAllowance bits) ((2 : ℝ) ^ penaltyExponent bits) s x

theorem sample_iff (bits : List Bool) (s : ℝ) (x : Fin (dimension bits) → ℝ) :
    Sample bits s x ↔
      (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i
        (CoerciveCriticalFibers.polynomial ((polynomial bits).map (Int.castRingHom ℝ))
          (degreeAllowance bits) s)) = 0) ∧
      (∑ i, x i ^ (2 * degreeAllowance bits + 2)) ≤ (2 : ℝ) ^ penaltyExponent bits ∧
      ((polynomial bits).eval₂ (Int.castRingHom ℝ) x) ^ 2 ≤ s * (2 : ℝ) ^ penaltyExponent bits := by
  simp only [Sample, Geometry.CoerciveApproximation.Sample,
    Geometry.CoercivePolynomialSampling.regularization, CoerciveCriticalFibers.polynomial,
    Geometry.CoercivePolynomialSampling.penalty, MvPolynomial.eval_map]

def EventuallySamples (bits : List Bool) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → ∃ x, Sample bits s x

/-- A concrete semantic reduction on all binary strings, with no finite-fiber,
simplicity, supplied root-radius, or supplied annihilator premise. -/
theorem correct (bits : List Bool) : bits ∈ ETR.language ↔ EventuallySamples bits := by
  rw [root_iff]
  exact Geometry.CoerciveRootRadius.root_iff_eventually_bounded_samples
    (polynomial bits) (degreeAllowance bits) (massAllowance bits)
    (polynomial_degree bits) (polynomial_mass bits)

/-- The source equation has a root within the implicit source radius. -/
theorem exists_root_bounded (bits : List Bool) (h : bits ∈ ETR.language) :
    ∃ x : Fin (dimension bits) → ℝ, (polynomial bits).eval₂ (Int.castRingHom ℝ) x = 0 ∧
      ∀ i, |x i| < (2 : ℝ) ^ radiusExponent bits :=
  Geometry.CoerciveRootRadius.exists_root_exp_bounded (polynomial bits)
    (degreeAllowance bits) (massAllowance bits) (polynomial_degree bits) (polynomial_mass bits)
    ((root_iff bits).mp h)

theorem radiusExponent_size (bits : List Bool) :
    (radiusExponent bits).size ≤ 128 * (CompactSource.size bits + 1) ^ 2 := by
  have h := CoerciveRadiusBits.massExponent_size_le (dimension bits)
    (degreeAllowance bits) (massAllowance bits)
  have hn := dimension_le_size bits
  have hs : (CompactSource.size bits).size ≤ CompactSource.size bits :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  unfold radiusExponent
  have ha : dimension bits + (degreeAllowance bits).size + (massAllowance bits).size + 4 ≤
      4 * (CompactSource.size bits + 1) := by unfold degreeAllowance massAllowance; omega
  exact h.trans (by calc
    _ ≤ 8 * (4 * (CompactSource.size bits + 1)) ^ 2 := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left ha 2)
    _ = _ := by ring)

theorem penaltyExponent_size (bits : List Bool) :
    (penaltyExponent bits).size ≤ 256 * (CompactSource.size bits + 1) ^ 2 := by
  have h := CoerciveRadiusBits.penaltyExponent_size_le (dimension bits)
    (degreeAllowance bits) (massAllowance bits)
  have hn := dimension_le_size bits
  have hs : (CompactSource.size bits).size ≤ CompactSource.size bits :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  unfold penaltyExponent
  have ha : dimension bits + (degreeAllowance bits).size + (massAllowance bits).size + 4 ≤
      4 * (CompactSource.size bits + 1) := by unfold degreeAllowance massAllowance; omega
  exact h.trans (by calc
    _ ≤ 16 * (4 * (CompactSource.size bits + 1)) ^ 2 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left ha 2)
    _ = _ := by ring)

/-- Both implicit numeric exponents have polynomial-size binary packets in
the original input length. This is a size statement, not an FP certificate. -/
theorem exponent_sizes_polynomial : ∃ A d : ℕ, ∀ bits : List Bool,
    (radiusExponent bits).size + (penaltyExponent bits).size ≤ A * (bits.length + 1) ^ d := by
  have hnorm := mem_FP_comp RationalSubstitutionBits.compiledTerm_mem_FP TermView.normalize_mem_FP
  obtain ⟨A, d, hA⟩ := hnorm.polyBounded_length.exists_le
  refine ⟨384 * (A + 1) ^ 2, 2 * d, ?_⟩
  intro bits
  have hsource : CompactSource.size bits + 1 ≤ (A + 1) * (bits.length + 1) ^ d := by
    have h := hA bits
    change CompactSource.size bits ≤ A * (bits.length + 1) ^ d at h
    have hp : 1 ≤ (bits.length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc
    _ ≤ 384 * (CompactSource.size bits + 1) ^ 2 := by
      have hr := radiusExponent_size bits
      have hp := penaltyExponent_size bits
      omega
    _ ≤ 384 * ((A + 1) * (bits.length + 1) ^ d) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end LeanCanny.ETR.CoerciveSourceSampling
