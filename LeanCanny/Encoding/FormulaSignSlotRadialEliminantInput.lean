/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientReadback
public import LeanCanny.Encoding.WordListFP
/-! # A total native coefficient frontend for the actual formal eliminant system

A packet pairs the original input with eight words: coordinate, row, unary
block-width request, source exponent word, homogeneous exponent, perturbation
exponent, target exponent, and modulus predecessor. Center and radius exponents
remain in the source exponent word. No eliminant evaluation is asserted.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantInput
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def field (i : ℕ) (q : List Bool) := WordList.get (pairSnd q) i
theorem field_FP (i : ℕ) : field i ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (g := WordList.reader)
    (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP (BinaryNatCode.encode i))) WordList.reader_FP)
  intro q
  simp only [Function.comp_apply, field, WordList.reader_packet]

noncomputable def spatialCount (q : List Bool) := FormulaSignSlotRadialFormalInput.spatial (pairFst q)
noncomputable def coordinate (q : List Bool) : Fin (spatialCount q) :=
  ⟨min (Nat.fromBitsLE (field 0 q)) (spatialCount q - 1), by
    have HM : 0 < spatialCount q := by dsimp only [spatialCount, FormulaSignSlotRadialFormalInput.spatial]; omega
    have H := Nat.min_le_right (Nat.fromBitsLE (field 0 q)) (spatialCount q - 1)
    omega⟩
noncomputable def row (q : List Bool) : Fin (spatialCount q + 1) :=
  ⟨min (Nat.fromBitsLE (field 1 q)) (spatialCount q), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
noncomputable def gradientRow (q : List Bool) : Fin (spatialCount q) :=
  ⟨(row q).val - 1, by
    have HM : 0 < spatialCount q := by dsimp only [spatialCount, FormulaSignSlotRadialFormalInput.spatial]; omega
    have H := (row q).isLt
    omega⟩
def width (q : List Bool) := (field 2 q).length

theorem spatialCount_unary : UnaryFn spatialCount := FormulaSignSlotRadialFormalInput.spatial_unary.comp pairFst_mem_FP
theorem coordinate_unary : UnaryFn (fun q => (coordinate q).val) :=
  UnaryFn.fromBitsLE_min (field_FP 0) (spatialCount_unary.sub (UnaryFn.const 1))
theorem row_unary : UnaryFn (fun q => (row q).val) := UnaryFn.fromBitsLE_min (field_FP 1) spatialCount_unary
theorem gradientRow_unary : UnaryFn (fun q => (gradientRow q).val) := row_unary.sub (UnaryFn.const 1)
theorem width_unary : UnaryFn width := UnaryFn.length (field_FP 2)
theorem full_dimension_unary : UnaryFn (fun q => FormulaSignSlotRadialEliminantRows.dimension (pairFst q)) :=
  (spatialCount_unary.add (UnaryFn.const 4)).add (FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP)

noncomputable def value (q : List Bool) :=
  if (row q).val = 0 then
    FormulaSignSlotRadialEliminantCoefficientNative.coordinateValue pairFst width
      (field 3) (field 4) (field 5) (field 6) (field 7) coordinate q
  else FormulaSignSlotRadialEliminantCoefficientNative.gradientValue pairFst width
      (field 3) (field 4) (field 5) (field 6) (field 7) gradientRow q

theorem evaluator : SpaceFunction value := by
  have EA := SpaceFunction.ofFP _ (FormulaSignSlotRadialEliminantCoefficientNative.coordinate_value_FP
    pairFst pairFst_mem_FP width width_unary (field 3) (field 4) (field 5) (field 6) (field 7)
    (field_FP 3) (field_FP 4) (field_FP 5) (field_FP 6) (field_FP 7) coordinate coordinate_unary)
  have EB := FormulaSignSlotRadialEliminantCoefficientNative.gradient_evaluator pairFst pairFst_mem_FP
    width width_unary (field 3) (field 4) (field 5) (field 6) (field 7)
    (field_FP 3) (field_FP 4) (field_FP 5) (field_FP 6) (field_FP 7) gradientRow gradientRow_unary
  have H := SpaceFunction.branch (fun q => decide ((row q).val = 0))
    (FPPred.eq row_unary (UnaryFn.const 0)).flag_mem_FP EA EB
  exact H.congr (funext fun q => by
    by_cases hz : (row q).val = 0 <;> simp only [value, hz, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true])

noncomputable def exponent (q : List Bool) :=
  FormulaSignSlotRadialEliminantRows.exponent
    ((FormulaSignSlotRadialEliminantCoefficientNative.homogeneousExponent pairFst width (field 3) (field 4) q).mapDomain
      CoerciveCriticalHomogenization.layout)
    (Nat.fromBitsLE (field 5 q)) (Nat.fromBitsLE (field 6 q))
    (FormulaSignSlotRadialEliminantCoefficientQuery.radius (pairFst q)
      (FormulaSignSlotRadialEliminantCoefficientNative.sourceExponent pairFst width (field 3) q))
    (FormulaSignSlotRadialEliminantCoefficientQuery.center (pairFst q)
      (FormulaSignSlotRadialEliminantCoefficientNative.sourceExponent pairFst width (field 3) q))

attribute [local irreducible] FormulaSignSlotRadialEliminantRows.polynomial
  FormulaSignSlotRadialEliminantRows.system

theorem correct (q : List Bool) : value q = residueBits
    (((FormulaSignSlotRadialEliminantRows.polynomial (pairFst q) (coordinate q) (row q)).coeff (exponent q) : ℤ) :
      ZMod (Nat.fromBitsLE (field 7 q) + 1)) := by
  by_cases hz : (row q).val = 0
  · have HR : (CoerciveCriticalHomogenization.layout none : Fin (spatialCount q + 1)) = row q := by
      apply Fin.ext
      exact hz.symm
    rw [value, ite_eq_left hz]
    exact (FormulaSignSlotRadialEliminantCoefficientNative.coordinateValue_correct pairFst width
      (field 3) (field 4) (field 5) (field 6) (field 7) coordinate q).trans
      (congrArg (fun r : Fin (spatialCount q + 1) => residueBits
        (((FormulaSignSlotRadialEliminantRows.polynomial (pairFst q) (coordinate q) r).coeff (exponent q) : ℤ) :
          ZMod (Nat.fromBitsLE (field 7 q) + 1))) HR)

  · have HR : CoerciveCriticalHomogenization.layout (some (gradientRow q)) = row q := by
      apply Fin.ext
      change (row q).val - 1 + 1 = (row q).val
      omega
    rw [value, ite_eq_right hz]
    exact (FormulaSignSlotRadialEliminantCoefficientNative.gradientValue_correct pairFst width
      (field 3) (field 4) (field 5) (field 6) (field 7) gradientRow q (coordinate q)).trans
      (congrArg (fun r : Fin (spatialCount q + 1) => residueBits
        (((FormulaSignSlotRadialEliminantRows.polynomial (pairFst q) (coordinate q) r).coeff (exponent q) : ℤ) :
          ZMod (Nat.fromBitsLE (field 7 q) + 1))) HR)


theorem spatial_homogeneous (q : List Bool) :
    (FormulaSignSlotRadialEliminantRows.system (pairFst q) (coordinate q) (row q)).IsHomogeneous
      (CoerciveCriticalHomogenization.finDegree (degreeBudget (pairFst q)) (row q)) :=
  FormulaSignSlotRadialEliminantRows.spatial_homogeneous _ _ _

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantInput
