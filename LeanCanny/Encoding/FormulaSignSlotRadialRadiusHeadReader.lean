/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadEvaluation
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientNative
public import LeanCanny.Algebra.FixedWidthBivariateReader
/-! # The actual radius head as a native univariate over packed formal center coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadReader
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def original (c : List Bool) := pairFst c
def tau (c : List Bool) := pairFst (pairSnd c)
def eta (c : List Bool) := pairSnd (pairSnd c)
noncomputable def arity (c : List Bool) := d (pairFst (original c))
noncomputable def width (c : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (original c)
noncomputable def degree (c : List Bool) := FormulaSignSlotRadialEliminantPacked.resultDegree (original c)
noncomputable def polynomial (c : List Bool) : Polynomial (MvPolynomial (Fin (arity c)) ℤ) := FormulaSignSlotRadialRadiusHeadEvaluation.radiusPolynomial
  (original c) (Nat.fromBitsLE (tau c)) (Nat.fromBitsLE (eta c))

def query (z : List Bool) := pair (pair (pair
  (original (FixedWidthBivariateReader.origin z))
  (WordList.encode [tau (FixedWidthBivariateReader.origin z),eta (FixedWidthBivariateReader.origin z),pairSnd (pairSnd z)]))
  (pairFst (pairSnd z))) (pairSnd (pairFst z))
theorem query_FP : query ∈ FP := by
  have HR := FixedWidthBivariateReader.origin_FP
  have HO : (fun z => original (FixedWidthBivariateReader.origin z)) ∈ FP :=
    mem_FP_comp (f := FixedWidthBivariateReader.origin) (g := original) HR pairFst_mem_FP
  have HT : (fun z => tau (FixedWidthBivariateReader.origin z)) ∈ FP :=
    mem_FP_comp (f := FixedWidthBivariateReader.origin) (g := tau) HR
      (mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP)
  have HE : (fun z => eta (FixedWidthBivariateReader.origin z)) ∈ FP :=
    mem_FP_comp (f := FixedWidthBivariateReader.origin) (g := eta) HR
      (mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP)
  have HV : (fun z => pairSnd (pairSnd z)) ∈ FP := mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP
  have HU : (fun z => pairFst (pairSnd z)) ∈ FP := mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP
  have HM : (fun z => pairSnd (pairFst z)) ∈ FP := mem_FP_comp (f := pairFst) (g := pairSnd) pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair HO (mem_FP_pair HT (mem_FP_pair HE (mem_FP_pair HV (constFn_mem_FP []))))) HU) HM

noncomputable def value := FormulaSignSlotRadialCenterCoefficientNative.value ∘ query
theorem evaluator : SpaceFunction value := FormulaSignSlotRadialCenterCoefficientNative.evaluator.precompose query query_FP
private noncomputable def entry (c : List Bool) (s t r : ℕ) (bits modulus : List Bool) :=
  residueBits (((FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).coeff
    (nativeExponent (Equiv.refl (Fin (d (pairFst c))))
      (FormulaSignSlotRadialEliminantPackingLayout.parameterWidth c) (Nat.fromBitsLE bits)) : ℤ) :
        ZMod (Nat.fromBitsLE modulus+1))
private theorem native_entry (q : List Bool) : FormulaSignSlotRadialCenterCoefficientNative.value q =
    entry (FormulaSignSlotRadialCenterCoefficientNative.origin q)
      (FormulaSignSlotRadialCenterCoefficientNative.selected 0 q)
      (FormulaSignSlotRadialCenterCoefficientNative.selected 1 q)
      (FormulaSignSlotRadialCenterCoefficientNative.selected 2 q)
      (FormulaSignSlotRadialCenterCoefficientNative.target q) (pairSnd q) :=
  FormulaSignSlotRadialCenterCoefficientNative.correct q
attribute [local irreducible] entry

theorem packet (q : List Bool) (u v : ℕ) :
    value (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((polynomial (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (width (pairFst q)) u)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1)) := by
  rw [value,Function.comp_apply,native_entry]
  simp only [query,FixedWidthBivariateReader.origin,FormulaSignSlotRadialCenterCoefficientNative.origin,
    FormulaSignSlotRadialCenterCoefficientNative.selected,FormulaSignSlotRadialCenterCoefficientNative.slot,
    FormulaSignSlotRadialCenterCoefficientNative.indices,FormulaSignSlotRadialCenterCoefficientNative.target,
    RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair,pairSnd_pair,WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  unfold entry polynomial arity
  rw [FormulaSignSlotRadialRadiusHeadEvaluation.coefficient]
  simp only [Nat.fromBitsLE_bits,width]

theorem radiusHeadReaderCoefficientDegree (c : List Bool) (s t r : ℕ) :
    ((FormulaSignSlotRadialRadiusHeadEvaluation.radiusPolynomial c s t).coeff r).totalDegree ≤
      FormulaSignSlotRadialEliminantPacked.resultDegree c := by
  rw [FormulaSignSlotRadialRadiusHeadEvaluation.coefficient]
  exact FormulaSignSlotRadialCenterCoefficient.degree c s t r

noncomputable def reader : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial arity width polynomial) :=
  FixedWidthBivariateReader.reader arity width polynomial value evaluator
    (FormulaSignSlotSource.dimension_unary.comp (mem_FP_comp (f := original) (g := pairFst) pairFst_mem_FP pairFst_mem_FP))
    (FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp pairFst_mem_FP)
    degree (fun c r => radiusHeadReaderCoefficientDegree (original c) (Nat.fromBitsLE (tau c)) (Nat.fromBitsLE (eta c)) r)
    (fun _ => FormulaSignSlotRadialEliminantPacked.result_fit _) packet

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadReader
