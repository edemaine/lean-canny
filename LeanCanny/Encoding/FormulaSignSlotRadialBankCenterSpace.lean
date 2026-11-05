/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterNumerator
/-! # Charged common-denominator access to the actual radial center tests -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSpace
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open FormulaSignSlotRadialBankCenterPolynomial (key family polynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterCoefficientSource.polynomial
  FormulaSignSlotRadialCenterCoefficientSource.arity FormulaSignSlotRadialCenterCoefficientSource.degree
  FormulaSignSlotRadialCenterCoefficientSource.width FormulaSignSlotRadialCenterCoefficientSource.mass

def sourceQuery (source : List Bool → List Bool) (q : List Bool) :=
  pair (pair (source (RationalSubstitution.IntegerBits.context q))
    (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
theorem sourceQuery_FP (source : List Bool → List Bool) (hs : source ∈ FP) : sourceQuery source ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP hs)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP
noncomputable def sourceRead (source : List Bool → List Bool) : List Bool → List Bool :=
  FormulaSignSlotRadialCenterCoefficientSource.coefficient ∘ sourceQuery source
theorem source_evaluator (source : List Bool → List Bool) (hs : source ∈ FP) : SpaceFunction (sourceRead source) :=
  FormulaSignSlotRadialCenterCoefficientSource.evaluator.precompose (sourceQuery source) (sourceQuery_FP source hs)

theorem source_packet (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) (r m : ℕ) (hm : 0 < m) :
    sourceRead source (pair (pair z (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((family B source refs).univariate.coefficient z r : ℤ) : ZMod m) := by
  simp only [sourceRead, Function.comp_apply, sourceQuery, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]
  rw [FormulaSignSlotRadialCenterCoefficientSource.packet]
  apply congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits,
      FixedWidthRationalSubstitutionBits.Family.coefficient, family,
      FixedWidthCommonDenominatorBits.Family.univariate, ← nativeExponent_refl]
    rw [FormulaSignSlotRadialCenterCoefficientSource.width]
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

def scalarQuery (B : Bank) (q : List Bool) := packet (key B (pairFst q)) (pairSnd q) 0 0
theorem scalarQuery_FP (B : Bank) (h : IntegralFramedBankQuery.Access B) : scalarQuery B ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := key B) pairFst_mem_FP
    (FormulaSignSlotRadialBankCenterPolynomial.key_FP B h)) pairSnd_mem_FP)
    (constFn_mem_FP (pair (BinaryNatCode.encode 0) (BinaryNatCode.encode 0)))
noncomputable def commonValue (B : Bank) (q : List Bool) := residueBits (IntegralMixedHistory.commonDenominator
    (IntegralMixedFramedBankDenominatorBits.state B.parameters B.plan B.data q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))
noncomputable def scalar (B : Bank) : List Bool → List Bool := commonValue B ∘ scalarQuery B

theorem scalar_evaluator (B : Bank) (h : IntegralFramedBankQuery.Access B) : SpaceFunction (scalar B) :=
  (IntegralMixedFramedCurrentQBankProductBits.common_evaluator B.parameters h.parameters B.plan B.data
    h.liftedData h.controls h.bounds).precompose (scalarQuery B) (scalarQuery_FP B h)

private theorem common_packet (B : Bank) (k mw : List Bool) : commonValue B (packet k mw 0 0) =
    residueBits (((atKey B.parameters B.plan B.data k).common : ℤ) : ZMod (Nat.fromBitsLE mw + 1)) := by
  have HI : IntegralMixedHistory.commonDenominator (IntegralMixedFramedBankDenominatorBits.state
      B.parameters B.plan B.data (packet k mw 0 0)) = (atKey B.parameters B.plan B.data k).common := by
    rw [IntegralMixedFramedBankSnapshotBits.common_at, IntegralMixedFramedBankSnapshotBits.packet_base]
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (packet k mw 0 0) = Nat.fromBitsLE mw + 1 := by
    simp only [IntegralMixedFramedCompanionQueryBits.callerModulus, packet, PaddedIntegralGeneratorSource.modulus,
      pairFst_pair, pairSnd_pair]
  exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) HI HM

attribute [local irreducible] commonValue

theorem scalar_packet (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) (m : ℕ) (hm : 0 < m) :
    scalar B (pair z (BinaryNatCode.encode (m - 1))) =
      residueBits (((family B source refs).denominator z : ℤ) : ZMod m) := by
  simp only [scalar, Function.comp_apply, scalarQuery, pairFst_pair, pairSnd_pair]
  rw [common_packet]
  exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
    (by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm])

noncomputable def access (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source refs : List Bool → List Bool) (hs : source ∈ FP) (hr : refs ∈ FP) :
    FixedWidthRationalSubstitutionBits.Access (family B source refs).univariate :=
  FixedWidthCommonDenominatorBits.access (family B source refs)
    (FormulaSignSlotRadialCenterCoefficientSource.arity_unary.comp hs)
    (FormulaSignSlotRadialCenterCoefficientSource.width_unary.comp hs)
    (sourceRead source) (FormulaSignSlotRadialBankCenterNumerator.value B source refs) (scalar B)
    (source_evaluator source hs) (FormulaSignSlotRadialBankCenterNumerator.evaluator B h source refs hs hr)
    (scalar_evaluator B h)
    (fun z r _ m hm => source_packet B source refs z r m hm)
    (fun z i _ k m hm => by
      have H := FormulaSignSlotRadialBankCenterNumerator.packet B source refs z i k (BinaryNatCode.encode (m - 1))
      apply H.trans
      exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
        (by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]))
    (scalar_packet B source refs)

theorem row_evaluator (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source refs target modulus : List Bool → List Bool)
    (hs : source ∈ FP) (hr : refs ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (family B source refs).targetArity
      (family B source refs).targetWidth (polynomial B source refs) target modulus) := by
  have E := FixedWidthCommonDenominatorBits.evaluator (family B source refs) (access B h source refs hs hr)
    target modulus (FormulaSignSlotRadialBankCenterPolynomial.targetArity_unary B h)
    (FormulaSignSlotRadialBankCenterPolynomial.width_unary B h source hs) ht hm
    (fun z => FormulaSignSlotRadialBankCenterPolynomial.support_fit B source refs z)
  exact E.congr (by
    funext q
    rw [FixedWidthRowBits.value, FormulaSignSlotRadialBankCenterPolynomial.family_polynomial]
    rfl)

end LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSpace
