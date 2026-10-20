/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermPowerFP
public import LeanCanny.ETR.CompactCoefficientSpace
public import LeanCanny.ETR.CompactCoefficientPadding
public import LeanCanny.Geometry.CubePolynomialMultiplication

/-! # Polynomial-space coefficients of compactified source powers

Writing a polynomially bounded power of the source and then compactifying it
computes the corresponding power of the compactified polynomial. Actual
source degrees, coefficient cancellation, and suspended child work are all
included. Positive powers retain the original arity, so zero-padded queries
access coefficients of the original compact polynomial directly.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactPowerCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Algebra.RationalSubstitution.Indexed Algebra.MatrixPower

def source (base : List Bool → List Bool) (power : List Bool → ℕ) : List Bool → List Bool :=
  TermPower.write base power

noncomputable def coefficient (base target : List Bool → List Bool) (power : List Bool → ℕ) (c : List Bool) : ℤ :=
  CompactCoefficient.coefficient (source base power) target c

noncomputable def value (base target modulus : List Bool → List Bool) (power : List Bool → ℕ) : List Bool → List Bool :=
  CompactCoefficient.value (source base power) target modulus

noncomputable def evaluator (base target modulus : List Bool → List Bool) (power : List Bool → ℕ)
    (hb : base ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) (hp : UnaryFn power) :
    SpaceFunction (value base target modulus power) :=
  CompactCoefficient.evaluator (source base power) target modulus (TermPower.write_mem_FP hb hp) ht hm

theorem source_term (base : List Bool → List Bool) (power : List Bool → ℕ) (c : List Bool) :
    TermView.term (source base power c) = (TermView.term (base c)).power (power c) := by
  rw [source, TermPower.write_correct, TermView.term_toBits]

theorem coefficient_eq_original (base target : List Bool → List Bool) (power : List Bool → ℕ)
    (c : List Bool) (hp : 0 < power c) (e : ℕ → ℕ)
    (ht : target c = FixedWidthNatVector.encode
      (CollectedCoefficient.dimension (source base power) c) (CompactCoefficient.width (source base power) c) e)
    (he : ∀ i < CollectedCoefficient.dimension (source base power) c,
      e i < 2 ^ CompactCoefficient.width (source base power) c)
    (hz : ∀ i, (TermView.term (base c)).arity ≤ i → e i = 0) :
    coefficient base target power c =
      (((TermView.term (base c)).compactPolynomial) ^ power c).coeff
        (exponentVector (TermView.term (base c)).arity e) := by
  have h := CompactCoefficient.coefficient_eq_of_encoded_target (source base power) target c e ht he
  have ha : (TermView.term (base c)).arity ≤ CollectedCoefficient.dimension (source base power) c := by
    have hdim := CollectedCoefficient.arity_le_dimension (source base power) c
    rw [source_term, Term.arity_power _ _ hp] at hdim
    exact hdim
  rw [source_term] at h
  rw [Term.coeff_cleared_padding _ _ _ (by rw [Term.arity_power _ _ hp]) ha e (by
    intro i hi _
    exact hz i hi), Term.finitePolynomial_power, Geometry.CubePolynomial.cleared_pow] at h
  exact h

theorem value_eq_original (base target modulus : List Bool → List Bool) (power : List Bool → ℕ)
    (c : List Bool) (hp : 0 < power c) (e : ℕ → ℕ)
    (ht : target c = FixedWidthNatVector.encode
      (CollectedCoefficient.dimension (source base power) c) (CompactCoefficient.width (source base power) c) e)
    (he : ∀ i < CollectedCoefficient.dimension (source base power) c,
      e i < 2 ^ CompactCoefficient.width (source base power) c)
    (hz : ∀ i, (TermView.term (base c)).arity ≤ i → e i = 0) :
    value base target modulus power c = residueBits
      (((((TermView.term (base c)).compactPolynomial) ^ power c).coeff
        (exponentVector (TermView.term (base c)).arity e) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have h := coefficient_eq_original base target power c hp e ht he hz
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1))) h

end LeanCanny.ETR.CompactPowerCoefficient
