/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FinitePolynomial
public import LeanCanny.ETR.CompiledRationalSource

/-! # Compact equation sets for every encoded ETR input

The existing verified equation compiler supplies the source term. Correctness
includes malformed-input defaults. These are semantic and degree results;
`CompactSourceCoefficient` supplies encoded coefficient residue access. The
subsequent perturbation/critical-point computation requires additional routines.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactSource
open Complexity
open LeanCanny.Encoding
open scoped BigOperators

noncomputable def term (bits : List Bool) : Term := TermView.term (RationalSubstitutionBits.compiledTerm bits)

noncomputable def polynomial (bits : List Bool) : MvPolynomial (Fin (term bits).arity) ℤ := (term bits).compactPolynomial

def size (bits : List Bool) : ℕ := (TermView.normalize (RationalSubstitutionBits.compiledTerm bits)).length

theorem size_eq (bits : List Bool) : size bits = (term bits).toData.size := by
  simp only [size, TermView.normalize_eq_term, Data.length_toBits, term]

theorem size_unary : UnaryFn size := by
  have h := mem_FP_comp RationalSubstitutionBits.compiledTerm_mem_FP TermView.normalize_mem_FP
  apply (UnaryFn.length h).of_eq
  intro bits
  simp only [size, Function.comp_apply]

def arityCode (bits : List Bool) : List Bool := BinaryNatCode.encode (size bits)
def degreeCode (bits : List Bool) : List Bool := BinaryNatCode.encode (4 * size bits ^ 2)

theorem arityCode_FP : arityCode ∈ FP := by
  have h := bits_mem_FP size_unary
  exact mem_FP_of_eq h (fun _ => rfl)

theorem degreeCode_FP : degreeCode ∈ FP := by
  have h := bits_mem_FP ((UnaryFn.const 4).mul (size_unary.pow_const 2))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem arity_le_code (bits : List Bool) : (term bits).arity ≤ Nat.fromBitsLE (arityCode bits) := by
  simp only [arityCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, size_eq]
  exact (term bits).arity_le_dataSize

theorem degree_le_code (bits : List Bool) : (polynomial bits).totalDegree ≤ Nat.fromBitsLE (degreeCode bits) := by
  simp only [degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, size_eq]
  exact (term bits).compactPolynomial_degree_size

def feasible (bits : List Bool) (epsilon : ℝ) : Set (Fin (term bits).arity → ℝ) :=
  {y | y ∈ (term bits).compactZeroSet epsilon}

theorem isCompact_feasible (bits : List Bool) (epsilon : ℝ) : IsCompact (feasible bits epsilon) :=
  (term bits).isCompact_compactZeroSet epsilon

theorem correct (bits : List Bool) :
    bits ∈ ETR.language ↔ ∃ epsilon : ℝ, 0 < epsilon ∧ (feasible bits epsilon).Nonempty := by
  rw [RationalSubstitutionBits.compiledTerm_correct]
  exact (term bits).exists_zero_iff_compact

theorem feasible_mono (bits : List Bool) {epsilon eta : ℝ} (h : eta ≤ epsilon) :
    feasible bits epsilon ⊆ feasible bits eta := (term bits).compactZeroSet_mono h

theorem correct_all_small_margins (bits : List Bool) :
    bits ∈ ETR.language ↔ ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ epsilon → (feasible bits eta).Nonempty := by
  rw [correct]
  constructor
  · rintro ⟨epsilon, he, hn⟩
    exact ⟨epsilon, he, fun _ _ hle => hn.mono (feasible_mono bits hle)⟩
  · rintro ⟨epsilon, he, hn⟩
    exact ⟨epsilon, he, hn epsilon he le_rfl⟩

theorem polynomial_degree (bits : List Bool) : (polynomial bits).totalDegree ≤ 4 * (term bits).toData.size ^ 2 :=
  (term bits).compactPolynomial_degree_size

theorem exists_linear_max (bits : List Bool) (h : bits ∈ ETR.language) (v : Fin (term bits).arity → ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ y ∈ feasible bits epsilon,
      ∀ z ∈ feasible bits epsilon, (∑ i, v i * z i) ≤ ∑ i, v i * y i := by
  obtain ⟨epsilon, he, hn⟩ := (correct bits).mp h
  exact ⟨epsilon, he, Geometry.CubePolynomial.exists_linear_max _ epsilon hn v⟩

end LeanCanny.ETR.CompactSource
