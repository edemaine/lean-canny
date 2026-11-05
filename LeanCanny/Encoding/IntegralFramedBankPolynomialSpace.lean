/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
/-! # Charged coefficient composition through the actual common bank denominator -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankPolynomialSpace
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open FormulaSignSlotRadialBankCenterPolynomial (key reference numerator denominator)
open IntegralFramedBankPolynomialModel (Source Access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def width (S : Source) (B : Bank) (read : List Bool → List Bool) (z : List Bool) :=
  (S.degree (read z) * IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (key B z)).size
noncomputable def family (S : Source) (B : Bank) (read refs : List Bool → List Bool) : FixedWidthCommonDenominatorBits.Family where
  sourceArity z := S.arity (read z)
  sourceWidth z := S.width (read z)
  targetArity z := (atKey B.parameters B.plan B.data (key B z)).count
  targetWidth := width S B read
  source z := S.polynomial (read z)
  denominator := denominator B
  numerator := numerator B refs
  source_fit z := S.fit (read z)

theorem width_unary (S : Source) (A : Access S) (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read : List Bool → List Bool) (hr : read ∈ FP) : UnaryFn (width S B read) := by
  have H : BinaryFn (fun z => S.degree (read z) * IntegralMixedFramedBankTermBits.maxPower
      B.parameters B.plan B.data (key B z)) :=
    BinaryFn.mul (A.degree.comp hr) ((IntegralMixedFramedBankTermBits.maxPower_binary B.parameters h.parameters
      B.plan B.data).comp (FormulaSignSlotRadialBankCenterPolynomial.key_FP B h))
  exact (UnaryFn.length H.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem targetArity_unary (S : Source) (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs : List Bool → List Bool) : UnaryFn (family S B read refs).targetArity :=
  (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters h.parameters B.plan B.data).comp
    (FormulaSignSlotRadialBankCenterPolynomial.key_FP B h)

theorem support_fit (S : Source) (B : Bank) (read refs : List Bool → List Bool) :
    ∀ z, ∀ e ∈ ((family S B read refs).polynomial z).support, ∀ i, e i < 2 ^ width S B read z :=
  (family S B read refs).support_fit (fun z => S.degree (read z))
    (fun z => IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (key B z))
    (fun z => S.polynomial_degree (read z))
    (fun _ _ => IntegralMixedFramedBankTermBits.numerator_degree _ _ _ _ _)
    (fun _ => Nat.lt_size_self _)

def sourceQuery := FormulaSignSlotRadialBankCenterSpace.sourceQuery
theorem sourceQuery_FP (read : List Bool → List Bool) (hr : read ∈ FP) : sourceQuery read ∈ FP :=
  FormulaSignSlotRadialBankCenterSpace.sourceQuery_FP read hr
noncomputable def sourceRead (S : Source) (A : Access S) (read : List Bool → List Bool) := A.coefficient ∘ sourceQuery read
theorem source_evaluator (S : Source) (A : Access S) (read : List Bool → List Bool) (hr : read ∈ FP) :
    SpaceFunction (sourceRead S A read) := A.evaluator.precompose (sourceQuery read) (sourceQuery_FP read hr)

theorem source_packet (S : Source) (A : Access S) (B : Bank) (read refs : List Bool → List Bool)
    (z : List Bool) (r m : ℕ) (hm : 0 < m) :
    sourceRead S A read (pair (pair z (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((family S B read refs).univariate.coefficient z r : ℤ) : ZMod m) := by
  simp only [sourceRead, Function.comp_apply, sourceQuery, FormulaSignSlotRadialBankCenterSpace.sourceQuery,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]
  rw [A.packet]
  apply congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits,
      FixedWidthRationalSubstitutionBits.Family.coefficient, family,
      FixedWidthCommonDenominatorBits.Family.univariate, ← nativeExponent_refl]
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

noncomputable def access (S : Source) (A : Access S) (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs : List Bool → List Bool) (hr : read ∈ FP) (hf : refs ∈ FP) :
    FixedWidthRationalSubstitutionBits.Access (family S B read refs).univariate :=
  FixedWidthCommonDenominatorBits.access (family S B read refs) (A.arity.comp hr) (A.width.comp hr)
    (sourceRead S A read) (IntegralFramedBankNumeratorAtWidth.value B refs (width S B read))
    (FormulaSignSlotRadialBankCenterSpace.scalar B)
    (source_evaluator S A read hr)
    (IntegralFramedBankNumeratorAtWidth.evaluator B h refs (width S B read) hf (width_unary S A B h read hr))
    (FormulaSignSlotRadialBankCenterSpace.scalar_evaluator B h)
    (fun z r _ m hm => source_packet S A B read refs z r m hm)
    (fun z i _ k m hm => by
      have H := IntegralFramedBankNumeratorAtWidth.packet B refs (width S B read) z i k (BinaryNatCode.encode (m - 1))
      exact H.trans (congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
        (by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm])))
    (fun z m hm => FormulaSignSlotRadialBankCenterSpace.scalar_packet B read refs z m hm)

theorem row_evaluator (S : Source) (A : Access S) (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs target modulus : List Bool → List Bool)
    (hr : read ∈ FP) (hf : refs ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (family S B read refs).targetArity
      (width S B read) (family S B read refs).polynomial target modulus) :=
  FixedWidthCommonDenominatorBits.evaluator (family S B read refs) (access S A B h read refs hr hf)
    target modulus (targetArity_unary S B h read refs) (width_unary S A B h read hr) ht hm (support_fit S B read refs)

end LeanCanny.Encoding.IntegralFramedBankPolynomialSpace
