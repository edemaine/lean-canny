/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveQueryCoefficient
public import LeanCanny.ETR.CoerciveInfinitesimalFamily
public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Dense rank access to every integer coercive sign query -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveQueryIndexed
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveSourceSampling CoerciveSymbolicSampling CoerciveInfinitesimalFamily
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

noncomputable def width (bits : List Bool) : ℕ := (allowance bits).size

theorem width_unary : UnaryFn width := CoerciveSymbolicBounds.allowance_unary.size

theorem width_le (bits : List Bool) : width bits ≤ CoercivePowerReaders.width bits := by
  have hs := CoercivePowerReaders.size_eq bits
  have hd := Nat.size_le_self (allowance bits)
  unfold width allowance degreeAllowance CoercivePowerReaders.width at *
  omega

theorem entry_le (bits : List Bool) (r i : ℕ) : FixedWidthPolynomial.entry (width bits) r i ≤ 2 * allowance bits := by
  have hpos : 0 < allowance bits := by unfold allowance; omega
  have hsize : 0 < (allowance bits).size := by
    have h := Nat.lt_size_self (allowance bits)
    by_contra hzero
    have he : (allowance bits).size = 0 := by omega
    rw [he, pow_zero] at h
    omega
  have hbound : 2 ^ ((allowance bits).size - 1) ≤ allowance bits := by
    by_contra h
    have he := Nat.size_le.mpr (show allowance bits < 2 ^ ((allowance bits).size - 1) by omega)
    omega
  have he : 2 ^ (allowance bits).size ≤ 2 * allowance bits := by
    rw [show (allowance bits).size = ((allowance bits).size - 1) + 1 by omega, pow_succ]
    omega
  exact (FixedWidthPolynomial.entry_lt (width bits) r i).le.trans he

noncomputable def target (input rank : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.repack (fun c => dimension (input c) + 1) (width ∘ input)
    (fun c => dimension (input c) + 1) (CoercivePowerReaders.width ∘ input) rank

theorem target_FP {input rank : List Bool → List Bool} (hi : input ∈ FP) (hr : rank ∈ FP) :
    target input rank ∈ FP :=
  FixedWidthQuery.repack_mem_FP ((dimension_unary.comp hi).add (UnaryFn.const 1)) (width_unary.comp hi)
    ((dimension_unary.comp hi).add (UnaryFn.const 1)) (CoercivePowerReaders.width_unary.comp hi) hr

theorem exponent_eq (input rank : List Bool → List Bool) (c : List Bool) :
    CoerciveQueryReaders.queryExponent input (target input rank) c =
      RationalSubstitution.Indexed.exponentVector (dimension (input c) + 1)
        (FixedWidthPolynomial.entry (width (input c)) (Nat.fromBitsLE (rank c))) := by
  rw [CoerciveQueryReaders.queryExponent_rank, ← FixedWidthPolynomial.nativeExponent_refl]
  exact FixedWidthPolynomial.nativeExponent_repack
    (Equiv.refl (Fin (dimension (input c) + 1))) (width ∘ input)
    (CoercivePowerReaders.width ∘ input) rank c (width_le (input c))

noncomputable def selected (input row : List Bool → List Bool) (c : List Bool) : ℕ :=
  min (Nat.fromBitsLE (row c)) (dimension (input c))

theorem selected_unary {input row : List Bool → List Bool} (hi : input ∈ FP) (hr : row ∈ FP) :
    UnaryFn (selected input row) := UnaryFn.fromBitsLE_min hr (dimension_unary.comp hi)

noncomputable def value (input row rank modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  if Nat.fromBitsLE (row c) < dimension (input c) then
    CoerciveQueryCoefficient.gradientValue input (target input rank) modulus (selected input row) c
  else if Nat.fromBitsLE (row c) = dimension (input c) then
    CoerciveQueryCoefficient.boundValue input (target input rank) modulus c
  else CoerciveQueryCoefficient.residualValue input (target input rank) modulus c

theorem evaluator {input row rank modulus : List Bool → List Bool}
    (hi : input ∈ FP) (hr : row ∈ FP) (ht : rank ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value input row rank modulus) := by
  have hn := bits_mem_FP (dimension_unary.comp hi)
  have hlt := BinaryNat.lt_fppred hr hn
  have heq : FPPred (fun c => Nat.fromBitsLE (row c) = dimension (input c)) := by
    simpa only [Nat.fromBitsLE_bits] using BinaryNat.eq_fppred hr hn
  have E := SpaceFunction.branch _ hlt.flag_mem_FP
    (CoerciveQueryCoefficient.gradientEvaluator hi (target_FP hi ht) hm (selected_unary hi hr))
    (SpaceFunction.branch _ heq.flag_mem_FP
      (CoerciveQueryCoefficient.boundEvaluator hi (target_FP hi ht) hm)
      (CoerciveQueryCoefficient.residualEvaluator hi (target_FP hi ht) hm))
  exact E.congr (funext fun c => by simp only [Nat.fromBitsLE_bits, value, decide_eq_true_eq])

theorem value_eq (input row rank modulus : List Bool → List Bool) (c : List Bool) :
    value input row rank modulus c = MatrixPower.residueBits
      (((integerQuery (input c) (queryIndex (input c) (Nat.fromBitsLE (row c)))).coeff
        (RationalSubstitution.Indexed.exponentVector (dimension (input c) + 1)
          (FixedWidthPolynomial.entry (width (input c)) (Nat.fromBitsLE (rank c)))) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold value queryIndex
  split_ifs with hlt heq
  · rw [CoerciveQueryCoefficient.gradient_value_eq input (target input rank) modulus (selected input row) c
      ⟨Nat.fromBitsLE (row c), hlt⟩ (by exact Nat.min_eq_left hlt.le), exponent_eq]
    rfl
  · rw [CoerciveQueryCoefficient.bound_value_eq, exponent_eq]
    simp only [heq, ne_eq, not_true_eq_false, decide_false, integerQuery]
  · rw [CoerciveQueryCoefficient.residual_value_eq, exponent_eq]
    simp only [decide_eq_true heq, integerQuery]

noncomputable def coefficient (bits : List Bool) (row r : ℕ) : ℤ :=
  (integerQuery bits (queryIndex bits row)).coeff
    (RationalSubstitution.Indexed.exponentVector (dimension bits + 1) (FixedWidthPolynomial.entry (width bits) r))

theorem source_eq (bits : List Bool) (row : ℕ) :
    RationalSubstitution.Indexed.source (dimension bits + 1)
      (FixedWidthPolynomial.count (dimension bits + 1) (width bits))
      (coefficient bits row) (FixedWidthPolynomial.entry (width bits)) = integerQuery bits (queryIndex bits row) := by
  apply FixedWidthPolynomial.indexed_source_eq
  intro e he i
  exact ((MvPolynomial.monomial_le_degreeOf i he).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (integerQuery_degree bits _))).trans_lt (Nat.lt_size_self _)

end LeanCanny.ETR.CoerciveQueryIndexed
