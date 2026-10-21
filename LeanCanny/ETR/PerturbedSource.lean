/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CompactSource
public import LeanCanny.Geometry.PerturbationPolynomials
public import LeanCanny.Geometry.AdditiveSubmersion

/-! # Compact perturbation families for every encoded ETR input

The compactified equation and cube constraints become weak polynomial
inequalities with independent additive shifts. The source is satisfiable
exactly when all sufficiently small positive radii admit a perturbed point.
The polynomial family has certified FP dimension, count, and degree bounds.
Regularity and the critical-point equations remain separate obligations.
-/

@[expose] public section

namespace LeanCanny.ETR.PerturbedSource
open Complexity
open LeanCanny.Encoding
open Geometry

abbrev Index (bits : List Bool) := PolynomialPerturbation.Constraint (Fin (CompactSource.term bits).arity)
abbrev Variable (bits : List Bool) := PolynomialPerturbation.Variable (Fin (CompactSource.term bits).arity)
abbrev Point (bits : List Bool) := (Fin (CompactSource.term bits).arity → ℝ) × (Index bits → ℝ)

def feasible (bits : List Bool) (epsilon delta : ℝ) : Set (Point bits) :=
  {z | z ∈ PolynomialPerturbation.perturbed (CompactSource.polynomial bits) epsilon delta}

theorem unperturbed_eq (bits : List Bool) (epsilon : ℝ) :
    PolynomialPerturbation.feasible (CompactSource.polynomial bits) epsilon = CompactSource.feasible bits epsilon := by
  rw [PolynomialPerturbation.feasible_eq]
  rfl

theorem nonempty_iff_eventually (bits : List Bool) (epsilon : ℝ) (he : 0 ≤ epsilon) :
    (CompactSource.feasible bits epsilon).Nonempty ↔ ∃ d : ℝ, 0 < d ∧
      ∀ delta : ℝ, 0 < delta → delta < d → (feasible bits epsilon delta).Nonempty := by
  have h := PolynomialPerturbation.nonempty_iff_eventually (CompactSource.polynomial bits) epsilon he
  rw [unperturbed_eq] at h
  exact h

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔ ∃ epsilon : ℝ, 0 < epsilon ∧
    ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d → (feasible bits epsilon delta).Nonempty := by
  rw [CompactSource.correct]
  apply exists_congr
  intro epsilon
  apply and_congr_right
  intro he
  exact nonempty_iff_eventually bits epsilon he.le

theorem correct_arbitrarily_small (bits : List Bool) : bits ∈ ETR.language ↔ ∃ epsilon : ℝ, 0 < epsilon ∧
    ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧ delta < eta ∧ (feasible bits epsilon delta).Nonempty := by
  rw [CompactSource.correct]
  apply exists_congr
  intro epsilon
  apply and_congr_right
  intro he
  have h := PolynomialPerturbation.nonempty_iff_arbitrarily_small (CompactSource.polynomial bits) epsilon he.le
  rw [unperturbed_eq] at h
  exact h

theorem nonempty_all_radii (bits : List Bool) (h : bits ∈ ETR.language) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ delta : ℝ, 0 ≤ delta → (feasible bits epsilon delta).Nonempty := by
  obtain ⟨epsilon, he, hn⟩ := (CompactSource.correct bits).mp h
  refine ⟨epsilon, he, fun delta hd => PolynomialPerturbation.nonempty_of_feasible _ _ _ hd ?_⟩
  rwa [unperturbed_eq]

theorem isCompact_feasible (bits : List Bool) (epsilon delta : ℝ) (he : 0 ≤ epsilon) (hd : 0 ≤ delta) :
    IsCompact (feasible bits epsilon delta) := PolynomialPerturbation.isCompact_perturbed _ _ _ he hd

theorem exists_max (bits : List Bool) (h : bits ∈ ETR.language) (g : Point bits → ℝ) (hg : Continuous g) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ delta : ℝ, 0 ≤ delta →
      ∃ z ∈ feasible bits epsilon delta, ∀ w ∈ feasible bits epsilon delta, g w ≤ g z := by
  obtain ⟨epsilon, he, hn⟩ := nonempty_all_radii bits h
  exact ⟨epsilon, he, fun delta hd => (isCompact_feasible bits epsilon delta he.le hd).exists_isMaxOn
    (hn delta hd) hg.continuousOn⟩

noncomputable def constraint (bits : List Bool) (i : Index bits) : MvPolynomial (Variable bits) ℤ :=
  PolynomialPerturbation.constraintPolynomial (CompactSource.polynomial bits) i

noncomputable def radius (bits : List Bool) : MvPolynomial (Variable bits) ℤ :=
  PolynomialPerturbation.radiusPolynomial (Fin (CompactSource.term bits).arity)

theorem polynomial_spec (bits : List Bool) (epsilon delta : ℝ) (z : Point bits) : z ∈ feasible bits epsilon delta ↔
    (∀ i, 0 ≤ (constraint bits i).eval₂ (Int.castRingHom ℝ) (PolynomialPerturbation.assignment epsilon delta z)) ∧
      (radius bits).eval₂ (Int.castRingHom ℝ) (PolynomialPerturbation.assignment epsilon delta z) = 0 :=
  PolynomialPerturbation.mem_perturbed_iff_polynomials _ _ _ _

theorem full_family_smooth (bits : List Bool) (epsilon : ℝ) :
    ContDiff ℝ ⊤ (PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon) :=
  PolynomialPerturbation.contDiff_parameterMap _ _

theorem full_family_derivative_surjective (bits : List Bool) (epsilon : ℝ) (z : Point bits) :
    Function.Surjective (fderiv ℝ (PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon) z) :=
  PolynomialPerturbation.parameterMap_derivative_surjective _ _ _

def countCode (bits : List Bool) : List Bool := BinaryNatCode.encode (2 + 2 * CompactSource.size bits)
def dimensionCode (bits : List Bool) : List Bool := BinaryNatCode.encode (4 + 3 * CompactSource.size bits)
def degreeCode (bits : List Bool) : List Bool := BinaryNatCode.encode (4 * CompactSource.size bits ^ 2 + 2)

theorem countCode_FP : countCode ∈ FP := by
  have h := bits_mem_FP ((UnaryFn.const 2).add ((UnaryFn.const 2).mul CompactSource.size_unary))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem dimensionCode_FP : dimensionCode ∈ FP := by
  have h := bits_mem_FP ((UnaryFn.const 4).add ((UnaryFn.const 3).mul CompactSource.size_unary))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem degreeCode_FP : degreeCode ∈ FP := by
  have h := bits_mem_FP (((UnaryFn.const 4).mul (CompactSource.size_unary.pow_const 2)).add (UnaryFn.const 2))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem count_le_code (bits : List Bool) : Fintype.card (Index bits) ≤ Nat.fromBitsLE (countCode bits) := by
  rw [PolynomialPerturbation.constraint_card, Fintype.card_fin]
  simp only [countCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  have h := (CompactSource.term bits).arity_le_dataSize
  omega

theorem dimension_le_code (bits : List Bool) : Fintype.card (Variable bits) ≤ Nat.fromBitsLE (dimensionCode bits) := by
  rw [PolynomialPerturbation.variable_card, Fintype.card_fin]
  simp only [dimensionCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  have h := (CompactSource.term bits).arity_le_dataSize
  omega

theorem constraint_degree_le_code (bits : List Bool) (i : Index bits) :
    (constraint bits i).totalDegree ≤ Nat.fromBitsLE (degreeCode bits) := by
  have h := PolynomialPerturbation.constraint_degree (CompactSource.polynomial bits) i
  have hp := CompactSource.polynomial_degree bits
  simp only [degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

theorem radius_degree_le_code (bits : List Bool) : (radius bits).totalDegree ≤ Nat.fromBitsLE (degreeCode bits) := by
  apply (PolynomialPerturbation.radius_degree (Fin (CompactSource.term bits).arity)).trans
  simp only [degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  omega

end LeanCanny.ETR.PerturbedSource
