/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSourceControls
public import LeanCanny.ETR.TermPowerFP
public import LeanCanny.ETR.CollectedCoefficientSpace
public import LeanCanny.ETR.FinitePolynomialCoefficientPadding
public import LeanCanny.Algebra.FixedWidthDerivativeSpace

/-! # Native coefficients of the squared compiled equation

The verified syntax power writer and collected coefficient evaluator stream q²
without polynomial multiplication or an external coefficient oracle. Exponent
queries are padded to the temporary syntax dimension and restored to the actual
source arity.
-/

@[expose] public section
namespace LeanCanny.ETR.CoercivePowerReaders
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra MatrixPower RationalSubstitution.Indexed
open CoerciveSourceSampling
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def squareSource : List Bool → List Bool :=
  TermPower.write RationalSubstitutionBits.compiledTerm (fun _ => 2)

theorem squareSource_FP : squareSource ∈ FP :=
  TermPower.write_mem_FP RationalSubstitutionBits.compiledTerm_mem_FP (UnaryFn.const 2)

theorem squareSource_term (bits : List Bool) :
    TermView.term (squareSource bits) = (CompactSource.term bits).power 2 := by
  rw [squareSource, TermPower.write_correct, TermView.term_toBits]
  rfl

def size (bits : List Bool) : ℕ := CollectedCoefficient.dimension squareSource bits
def width (bits : List Bool) : ℕ := size bits + 1

theorem size_unary : UnaryFn size := CollectedCoefficient.dimension_unary squareSource_FP
theorem width_unary : UnaryFn width := size_unary.add (UnaryFn.const 1)

theorem dimension_le_size (bits : List Bool) : dimension bits ≤ size bits := by
  have h := CollectedCoefficient.arity_le_dimension squareSource bits
  rw [squareSource_term, Term.arity_power _ 2 (by decide)] at h
  exact h

theorem size_eq (bits : List Bool) : size bits = 2 * CompactSource.size bits + 34 := by
  rw [size, CollectedCoefficient.dimension, TermView.normalize_eq_term, squareSource_term,
    Data.length_toBits, CompactSource.size_eq]
  simp only [Term.power, Term.dataSize_mul, Term.dataSize_const_one]
  omega

theorem squareDegree_lt (bits : List Bool) : 2 * degreeAllowance bits + 1 < 2 ^ width bits := by
  have hs := size_eq bits
  have hw : 2 * degreeAllowance bits + 1 < width bits := by unfold width degreeAllowance; omega
  exact hw.trans Nat.lt_two_pow_self

attribute [local irreducible] squareSource CoerciveSourceSampling.dimension size width

noncomputable def exponent (input target : List Bool → List Bool) (c : List Bool) :
    Fin (dimension (input c)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => FixedWidthQuery.coordinate (width ∘ input) target c i.val)

noncomputable def targetWord (input target : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.repack (dimension ∘ input) (width ∘ input) (size ∘ input) (width ∘ input) target

noncomputable def value (input target modulus : List Bool → List Bool) : List Bool → List Bool :=
  CollectedCoefficient.value (squareSource ∘ input) (targetWord input target) modulus

theorem targetWord_FP {input target : List Bool → List Bool} (hi : input ∈ FP) (ht : target ∈ FP) :
    targetWord input target ∈ FP :=
  FixedWidthQuery.repack_mem_FP (dimension_unary.comp hi) (width_unary.comp hi)
    (size_unary.comp hi) (width_unary.comp hi) ht

theorem evaluator {input target modulus : List Bool → List Bool}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value input target modulus) :=
  CollectedCoefficient.evaluator _ _ _ (mem_FP_comp hi squareSource_FP) (targetWord_FP hi ht) hm

theorem value_eq (input target modulus : List Bool → List Bool) (c : List Bool) :
    value input target modulus c = residueBits
      ((((polynomial (input c)) ^ 2).coeff (exponent input target c) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let e := FixedWidthQuery.entry (dimension ∘ input) (width ∘ input) target c
  have hfit : ∀ i < size (input c), e i < 2 ^ (size (input c) + 1) := by
    intro i _
    dsimp only [e, FixedWidthQuery.entry, Function.comp_apply]
    split_ifs
    · unfold FixedWidthQuery.coordinate
      exact (Nat.fromBitsLE_lt_pow_length _).trans_le (Nat.pow_le_pow_right (by decide)
        ((List.length_take_le _ _).trans (by rw [Function.comp_apply, width])))
    · exact Nat.two_pow_pos _
  have hd : CollectedCoefficient.dimension (squareSource ∘ input) c = size (input c) := by
    rw [size]; rfl
  have ht : targetWord input target c = FixedWidthNatVector.encode
      (CollectedCoefficient.dimension (squareSource ∘ input) c)
      (CollectedCoefficient.dimension (squareSource ∘ input) c + 1) e := by
    rw [hd]
    simp only [targetWord, FixedWidthQuery.repack, Function.comp_apply, width]
    rfl
  have h := CollectedCoefficient.coefficient_eq_of_encoded_target (squareSource ∘ input)
    (targetWord input target) c e ht (by simpa only [hd] using hfit)
  rw [hd] at h
  rw [show TermView.term ((squareSource ∘ input) c) = (CompactSource.term (input c)).power 2 from
    squareSource_term (input c)] at h
  change CollectedCoefficient.coefficient (squareSource ∘ input) (targetWord input target) c =
    (Term.finitePolynomial (size (input c)) ((CompactSource.term (input c)).power 2)).coeff
      (exponentVector (size (input c)) e) at h
  rw [Term.coeff_finitePolynomial_padding _ (dimension (input c)) (size (input c))
    (by rw [Term.arity_power _ 2 (by decide), CoerciveSourceSampling.dimension]) (dimension_le_size (input c)) e
    (by intro i hi _; simp only [e, FixedWidthQuery.entry, Function.comp_apply]; exact ite_eq_right (by omega)),
    Term.finitePolynomial_power] at h
  have he : exponentVector (dimension (input c)) e = exponent input target c := by
    ext i
    simp only [exponentVector, exponent, Finsupp.coe_equivFunOnFinite_symm,
      e, FixedWidthQuery.entry, Function.comp_apply, i.isLt, ite_true]
  rw [he] at h
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1))) h

/-- Raw rank words give the usual native fixed-width exponent. -/
theorem exponent_rank (input target : List Bool → List Bool) (c : List Bool) :
    exponent input target c = FixedWidthPolynomial.nativeExponent
      (Equiv.refl (Fin (dimension (input c)))) (width (input c)) (Nat.fromBitsLE (target c)) := by
  ext i
  simp only [exponent, FixedWidthPolynomial.nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
    Function.comp_apply, Equiv.refl_apply, FixedWidthQuery.coordinate]
  rw [FixedWidthPolynomial.entry_eq_digit, BinaryNat.value_take, FixedWidthPolynomial.drop_value]

end LeanCanny.ETR.CoercivePowerReaders
