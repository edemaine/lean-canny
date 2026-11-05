/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueNativeFamily
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTestSource
/-! # Closed native coefficients of the actual packed radial value certificate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSpace
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance radialValueSpaceParameterNeZero (z : List Bool) :
    NeZero (FormulaSignSlotRadialCenterValueTestQuery.parameterCount z) :=
  ⟨by unfold FormulaSignSlotRadialCenterValueTestQuery.parameterCount FormulaSignSlotRadialCenterValuePacking.arity; omega⟩

noncomputable def Fits (z : List Bool) := Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.parameter z) <
  FormulaSignSlotRadialCenterValuePacking.box (FormulaSignSlotRadialCenterValueTestQuery.base z)
theorem fits_FP : FPPred Fits := (BinaryFn.fromBits FormulaSignSlotRadialCenterValueTestQuery.parameter_FP).lt
  (FormulaSignSlotRadialCenterValuePacking.box_binary.comp FormulaSignSlotRadialCenterValueTestQuery.base_FP)
noncomputable def testValue (z : List Bool) := if Fits z then FormulaSignSlotRadialCenterValueTestSource.value z else []
theorem testValue_evaluator : SpaceFunction testValue := by
  have E := SpaceFunction.branch (fun z => decide (Fits z)) fits_FP.flag_mem_FP
    FormulaSignSlotRadialCenterValueTestSource.evaluator (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [testValue, decide_eq_true_eq])

private theorem packed_coefficient {A : ℕ} (p : Polynomial (MvPolynomial (Fin A) ℤ)) (W k : ℕ)
    (h : (TriplePolynomialParameterFlatten.one p).totalDegree < 2 ^ W)
    (hk : k < count (A + 1) W) :
    (FixedWidthKronecker.encode (A + 1) W (TriplePolynomialParameterFlatten.one p)).coeff k =
      (p.coeff (nativeExponent (Equiv.refl (Fin (A + 1))) W k 0)).coeff
        (nativeExponent (Equiv.refl (Fin (A + 1))) W k).tail := by
  have HC := FixedWidthKronecker.native_coefficient (Equiv.refl (Fin (A + 1))) W
    (TriplePolynomialParameterFlatten.one p).totalDegree (TriplePolynomialParameterFlatten.one p) le_rfl h k hk
  have HE : (FixedWidthKronecker.encode (A + 1) W (TriplePolynomialParameterFlatten.one p)).coeff k =
      (TriplePolynomialParameterFlatten.one p).coeff (nativeExponent (Equiv.refl _) W k) := by
    simpa [FixedWidthKronecker.native] using HC
  rw [HE]
  have HX := TriplePolynomialParameterFlatten.one_coefficient p
    (nativeExponent (Equiv.refl (Fin (A + 1))) W k 0) (nativeExponent (Equiv.refl (Fin (A + 1))) W k).tail
  simpa only [Finsupp.cons_tail] using HX

private theorem parameter_fit (z : List Bool) :
    (TriplePolynomialParameterFlatten.one ((FormulaSignSlotRadialFormalCenter.polynomial
      (FormulaSignSlotRadialCenterValueTestQuery.original z)).coeff
        (FormulaSignSlotRadialCenterValueTestSource.spatial z))).totalDegree <
      2 ^ FormulaSignSlotRadialCenterValueTestQuery.parameterWidth z :=
  (FormulaSignSlotRadialCenterValueBounds.test_degree _ _).trans_lt
    (FormulaSignSlotRadialCenterValueNativeFamily.test_fit (FormulaSignSlotRadialCenterValueTestQuery.base z))

private theorem test_coefficient_eq (z : List Bool) :
    FormulaSignSlotRadialCenterValueNativeFamily.family.testCoefficient z = residueBits
      (((FixedWidthKronecker.encode (FormulaSignSlotRadialCenterValueTestQuery.parameterCount z)
        (FormulaSignSlotRadialCenterValueTestQuery.parameterWidth z) (TriplePolynomialParameterFlatten.one
        ((FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueTestQuery.original z)).coeff
          (FormulaSignSlotRadialCenterValueTestSource.spatial z)))).coeff
            (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.parameter z))) :
              ZMod (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1)) := rfl

theorem testValue_correct (z : List Bool) : testValue z =
    FormulaSignSlotRadialCenterValueNativeFamily.family.testCoefficient z := by
  by_cases H : Fits z
  · rw [testValue, ite_eq_left H, FormulaSignSlotRadialCenterValueTestSource.coefficient,
      test_coefficient_eq]
    exact congrArg (fun a : ℤ => residueBits (a :
      ZMod (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1)))
        (packed_coefficient _ _ _ (parameter_fit z) H).symm
  · rw [testValue, ite_eq_right H, test_coefficient_eq]
    have HZ : (FixedWidthKronecker.encode _ _ (TriplePolynomialParameterFlatten.one
        ((FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueTestQuery.original z)).coeff
          (FormulaSignSlotRadialCenterValueTestSource.spatial z)))).coeff
            (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.parameter z)) = 0 :=
      FixedWidthKronecker.coefficient_of_ge _ _ _ (fun e he i =>
        ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
          (parameter_fit z)) _ (Nat.le_of_not_gt H)

    exact (congrArg (fun a : ℤ => residueBits (a :
      ZMod (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1))) HZ).symm

theorem test_evaluator : SpaceFunction FormulaSignSlotRadialCenterValueNativeFamily.family.testCoefficient :=
  testValue_evaluator.congr (funext testValue_correct)

noncomputable def reader : CertifiedPolynomial.BivariateReader
    FormulaSignSlotRadialCenterValueNativeFamily.family.affine.homogeneous.annihilator :=
  IntegerGridValueGramBits.Family.reader FormulaSignSlotRadialCenterValueNativeFamily.family
    FormulaSignSlotRadialCenterValueNativeFamily.controls FormulaSignSlotRadialCenterValuePacking.box
    FormulaSignSlotRadialCenterValuePacking.box_binary
    FormulaSignSlotRadialCenterValueNativeFamily.coordinate_inner_degree
    FormulaSignSlotRadialCenterValueNativeFamily.test_inner_degree
    FormulaSignSlotRadialCenterValueCoordinateReader.evaluator test_evaluator

theorem evaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient FormulaSignSlotRadialCenterValuePacking.polynomial) := by
  have H : FormulaSignSlotRadialCenterValueNativeFamily.family.affine.homogeneous.annihilator =
      FormulaSignSlotRadialCenterValuePacking.polynomial := funext FormulaSignSlotRadialCenterValueNativeFamily.annihilator_eq
  rw [← H]
  exact reader.evaluator

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSpace
