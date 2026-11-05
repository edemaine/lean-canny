/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutFamily
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalReader
public import LeanCanny.Algebra.FixedWidthBivariateRebox
public import LeanCanny.Algebra.PolynomialFamilyProductSpace
/-! # Original arbitrary-modulus readers in the larger actual cut box

The principal stream here is the unsigned determinant used by DomainSquarefree.
The output box is chosen before any multiplication or principal power.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutReader
open LeanCanny.Algebra LeanCanny.Computation Polynomial PrincipalSubresultant MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def reader := FixedWidthBivariateRebox.reader
  FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterPrincipalFamily.width
  FormulaSignSlotRadialCenterBranchCutFamily.width FormulaSignSlotRadialCenterPrincipalFamily.inputBound
  FormulaSignSlotRadialCenterPrincipalFamily.polynomial FormulaSignSlotRadialCenterPrincipalReader.reader
  FormulaSignSlotRadialCenterPrincipalFamily.arity_unary FormulaSignSlotRadialCenterPrincipalFamily.width_unary
  FormulaSignSlotRadialCenterBranchCutFamily.width_unary FormulaSignSlotRadialCenterPrincipalFamily.polynomial_degree
  FormulaSignSlotRadialCenterPrincipalFamily.input_fit FormulaSignSlotRadialCenterBranchCutFamily.input_fit

noncomputable def family : PolynomialPrincipalCoefficientBits.Family where
  left := FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.arity
    FormulaSignSlotRadialCenterBranchCutFamily.width FormulaSignSlotRadialCenterPrincipalFamily.polynomial
  right c := (FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.arity
    FormulaSignSlotRadialCenterBranchCutFamily.width FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).derivative
  leftDegree := FormulaSignSlotRadialCenterPrincipalFamily.degree
  rightDegree c := FormulaSignSlotRadialCenterPrincipalFamily.degree c - 1
noncomputable def access : PolynomialPrincipalCoefficientBits.Access family where
  left := reader
  right := CertifiedPolynomial.BivariateDerivative.reader reader
  leftDegree := FormulaSignSlotRadialCenterPrincipalFamily.degree_binary
  rightDegree := FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.sub (BinaryFn.const 1)

noncomputable def leading (c : List Bool) : Polynomial ℤ :=
  (family.left c).coeff (FormulaSignSlotRadialCenterPrincipalFamily.degree c)
noncomputable def minor := PolynomialPrincipalMinorBits.determinant (PolynomialPrincipalCoefficientBits.minor family)

def leadingQuery (q : List Bool) := pair (pair (context q) (pairSnd q))
  (pair (BinaryNat.normalize (selectedDegree q))
    (BinaryNatCode.encode (FormulaSignSlotRadialCenterPrincipalFamily.degree (context q))))
theorem leadingQuery_FP : leadingQuery ∈ FP := by
  have HD : BinaryFn (fun q => FormulaSignSlotRadialCenterPrincipalFamily.degree (context q)) :=
    FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.comp RationalSubstitution.IntegerBits.context_mem_FP
  exact mem_FP_pair
    (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP BinaryNat.normalize_mem_FP)
      HD.bits_mem_FP)

theorem leading_evaluator : SpaceFunction (PrimitivePairBits.coefficient leading) := by
  have E := reader.evaluator.precompose leadingQuery leadingQuery_FP
  refine E.congr (funext fun q => ?_)
  dsimp only [Function.comp_apply, leadingQuery]
  rw [BinaryNat.normalize_eq_bits]
  exact (reader.coefficient_eq (pair (context q) (pairSnd q))
    (Nat.fromBitsLE (selectedDegree q)) (FormulaSignSlotRadialCenterPrincipalFamily.degree (context q))).trans (by
      unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
      apply congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
      · simp only [pairFst_pair, leading, family]
      · simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair])

theorem minor_evaluator : SpaceFunction (PrimitivePairBits.coefficient minor) := by
  have E := PolynomialPrincipalMinorBits.evaluator (PolynomialPrincipalCoefficientBits.minorAccess access)
  refine E.congr (funext fun q => ?_)
  rw [PolynomialPrincipalMinorBits.value_eq]
  rfl

theorem leading_eq (c : List Bool) : leading c = FixedWidthKronecker.encode
    (FormulaSignSlotRadialCenterPrincipalFamily.arity c) (FormulaSignSlotRadialCenterBranchCutFamily.width c)
      ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).coeff
        (FormulaSignSlotRadialCenterPrincipalFamily.degree c)) := by
  change ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).map _).coeff _ = _
  rw [Polynomial.coeff_map]

theorem minor_eq (r : List Bool)
    (hk : Nat.fromBitsLE (pairSnd r) < FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r)) :
    minor r = FixedWidthKronecker.encode
      (FormulaSignSlotRadialCenterPrincipalFamily.arity (pairFst r))
      (FormulaSignSlotRadialCenterBranchCutFamily.width (pairFst r))
        (FormulaSignSlotRadialCenterBranchCutFamily.principal (pairFst r) (Nat.fromBitsLE (pairSnd r))) := by
  dsimp only [minor, PolynomialPrincipalMinorBits.determinant, PolynomialPrincipalCoefficientBits.minor, family]
  rw [← psc_eq_minor]
  rw [Nat.min_eq_left (by omega)]
  change psc ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial (pairFst r)).map _)
    ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial (pairFst r)).map _).derivative _ _ _ = _
  rw [Polynomial.derivative_map, psc_map_map]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutReader
