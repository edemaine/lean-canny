/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSymbolicBounds
public import LeanCanny.Algebra.InfinitesimalRootPSPACE

/-! # The concrete eventual root-sign family for encoded coercive sampling -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveInfinitesimalFamily
open LeanCanny.Algebra LeanCanny.Encoding
open CoerciveSourceSampling CoercivePreparationControls CoerciveSymbolicSampling CoerciveSymbolicBounds
open Polynomial
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix
attribute [local irreducible] CoercivePreparationControls.referenceCode CoercivePreparationControls.referenceExponent
attribute [local irreducible] CoerciveSymbolicBounds.queryDegree CoerciveSymbolicBounds.queryMassExponent

noncomputable def queryIndex (bits : List Bool) (i : ℕ) : Query bits :=
  if hi : i < dimension bits then .inl ⟨i, hi⟩ else .inr (decide (i ≠ dimension bits))

noncomputable def rootFamily : DyadicPolynomialBits.Family where
  polynomial bits := (family bits).parameter
  degree := referenceCode
  parameterDegree := referenceCode
  exponent _ := []
  mass bits := BinaryNatCode.encode (2 * referenceExponent bits + 1)
  polynomial_degree bits := by simpa only [referenceCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] using parameter_degree bits
  coefficient_degree bits i := by simpa only [referenceCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] using parameter_inner_degree bits i
  coefficient_mass bits i := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (NestedMass.coeff_le _ _).trans (parameter_mass bits)

def wanted (negative : Bool) : SignType := if negative then -1 else 0

noncomputable def pattern (left right : Bool) (bits : List Bool) (i : ℕ) : SignType :=
  if i < dimension bits then 0 else if i = dimension bits then wanted left else wanted right

noncomputable def signFamily (left right : Bool) : DyadicSignPatternBits.Family where
  root := rootFamily
  polynomial bits i := clearedQuery bits (queryIndex bits i)
  pattern := pattern left right
  count bits := BinaryNatCode.encode (dimension bits + 2)
  degree bits := BinaryNatCode.encode (queryDegree bits)
  parameterDegree bits := BinaryNatCode.encode (queryDegree bits)
  mass bits := BinaryNatCode.encode (queryMassExponent bits)
  polynomial_degree bits i := by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using cleared_degree bits (queryIndex bits i)
  coefficient_degree bits i k := by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using cleared_inner_degree bits (queryIndex bits i) k
  coefficient_mass bits i k := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (NestedMass.coeff_le _ _).trans (cleared_mass bits (queryIndex bits i))

theorem root_controls : DyadicPolynomialBits.ControlsPolyTime rootFamily := by
  constructor
  · change referenceCode ∈ FP
    exact referenceCode_mem_FP
  · change referenceCode ∈ FP
    exact referenceCode_mem_FP
  · exact constFn_mem_FP []
  · change (fun bits => BinaryNatCode.encode (2 * referenceExponent bits + 1)) ∈ FP
    exact (((BinaryFn.const 2).mul referenceExponent_binary).add (BinaryFn.const 1)).bits_mem_FP

theorem controls (left right : Bool) : DyadicSignPatternBits.ControlsPolyTime (signFamily left right) := by
  constructor
  · exact root_controls
  · change (fun bits => BinaryNatCode.encode (dimension bits + 2)) ∈ FP
    exact bits_mem_FP (dimension_unary.add (UnaryFn.const 2))
  · exact (dimension_unary.add (UnaryFn.const 2)).of_eq (fun bits => by
      simp only [signFamily, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  · change (fun bits => BinaryNatCode.encode (queryDegree bits)) ∈ FP
    exact queryDegree_binary.bits_mem_FP
  · change (fun bits => BinaryNatCode.encode (queryDegree bits)) ∈ FP
    exact queryDegree_binary.bits_mem_FP
  · change (fun bits => BinaryNatCode.encode (queryMassExponent bits)) ∈ FP
    exact queryMassExponent_binary.bits_mem_FP

noncomputable def patternReader (left right : Bool) (p : List Bool) : List Bool :=
  InfinitesimalSign.encode (pattern left right (pairFst p) (Nat.fromBitsLE (pairSnd p)))

theorem patternReader_mem_FP (left right : Bool) : patternReader left right ∈ FP := by
  have hn := bits_mem_FP (dimension_unary.comp pairFst_mem_FP)
  have hlt := BinaryNat.lt_fppred pairSnd_mem_FP hn
  have heq : FPPred (fun p => Nat.fromBitsLE (pairSnd p) = dimension (pairFst p)) := by
    apply ((BinaryNat.le_fppred pairSnd_mem_FP hn).and (BinaryNat.le_fppred hn pairSnd_mem_FP)).of_iff
    intro p
    simp only [Nat.fromBitsLE_bits]
    exact le_antisymm_iff.symm
  have h := hlt.ite_mem_FP (constFn_mem_FP [])
    (heq.ite_mem_FP (constFn_mem_FP (InfinitesimalSign.encode (wanted left)))
      (constFn_mem_FP (InfinitesimalSign.encode (wanted right))))
  apply mem_FP_of_eq h
  intro p
  simp only [Nat.fromBitsLE_bits]
  unfold patternReader pattern
  split_ifs <;> rfl

theorem root_ne_zero (bits : List Bool) : rootFamily.polynomial bits ≠ 0 := parameter_ne_zero bits

end LeanCanny.ETR.CoerciveInfinitesimalFamily
