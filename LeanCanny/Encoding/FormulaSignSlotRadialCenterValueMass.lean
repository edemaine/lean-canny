/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueNativeFamily
public import LeanCanny.Algebra.AffineValueGramHeight
/-! # Original integer coefficient mass of the actual formal radial value certificate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueMass
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

local instance radialValueMassParameterNeZero (c : List Bool) :
    NeZero (FormulaSignSlotRadialCenterValuePacking.arity c) :=
  ⟨by unfold FormulaSignSlotRadialCenterValuePacking.arity; omega⟩

noncomputable def coordinateBudget (c : List Bool) :=
  FormulaSignSlotRadialEliminantFormalMass.budget (FormulaSignSlotRadialCenterValuePacking.originalPacket c)
noncomputable def testBudget (c : List Bool) :=
  FormulaSignSlotRadialEliminantScalarMass.sourceSize (FormulaSignSlotRadialCenterValueLayout.original c)
noncomputable def rowBudget (c : List Bool) := FormulaSignSlotRadialCenterValuePacking.arity c *
  FormulaSignSlotRadialCenterValuePacking.width c + coordinateBudget c + testBudget c
noncomputable def budget (c : List Bool) := FormulaSignSlotRadialCenterValuePacking.arity c *
  FormulaSignSlotRadialCenterValuePacking.width c + ProjectiveValueGram.massExponent
    (FormulaSignSlotRadialCenterValueLayout.arity c) (FormulaSignSlotRadialCenterValueLayout.width c) (rowBudget c)

theorem coordinateBudget_binary : BinaryFn coordinateBudget :=
  FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp FormulaSignSlotRadialCenterValuePacking.originalPacket_FP
theorem testBudget_unary : UnaryFn testBudget := FormulaSignSlotRadialEliminantScalarMass.sourceSize_unary.comp
  FormulaSignSlotRadialCenterValueLayout.original_FP
theorem rowBudget_binary : BinaryFn rowBudget :=
  ((BinaryFn.ofUnary (FormulaSignSlotRadialCenterValuePacking.arity_unary.mul
    FormulaSignSlotRadialCenterValuePacking.width_unary)).add coordinateBudget_binary).add
      (BinaryFn.ofUnary testBudget_unary)
theorem budget_binary : BinaryFn budget :=
  (BinaryFn.ofUnary (FormulaSignSlotRadialCenterValuePacking.arity_unary.mul
    FormulaSignSlotRadialCenterValuePacking.width_unary)).add
      (ProjectiveValueGramBits.Family.massExponent_binary _
        FormulaSignSlotRadialCenterValueNativeFamily.controls rowBudget rowBudget_binary)

private theorem budget_coordinate (c : List Bool) (i : ℕ) :
    FormulaSignSlotRadialEliminantFormalMass.budget
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialCenterValueLayout.original c) i) =
        coordinateBudget c := by
  rw [coordinateBudget, FormulaSignSlotRadialCenterValuePacking.originalPacket,
    FormulaSignSlotRadialCoordinatePacket.writer_packet]
  simp only [FormulaSignSlotRadialEliminantFormalMass.budget, FormulaSignSlotRadialEliminantMass.resultBudget,
    FormulaSignSlotRadialEliminantMass.rowBudget, FormulaSignSlotRadialEliminantPackingLayout.columns,
    FormulaSignSlotRadialEliminantPackingLayout.parameterWidth, FormulaSignSlotRadialEliminantPackingLayout.columnExponent,
    FormulaSignSlotRadialEliminantPackingLayout.width, FormulaSignSlotRadialEliminantPackingLayout.spatial,
    FormulaSignSlotRadialEliminantPackingLayout.sourceDegree, FormulaSignSlotRadialEliminantPackingLayout.parameterDegree,
    FormulaSignSlotRadialCoordinatePacket.root]

private theorem nested_at (q c : List Bool) (hc : pairFst q = c)
    (i : Fin (N c + d c + 1)) (hi : (FormulaSignSlotRadialEliminantInput.coordinate q).val = i.val)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (((((FormulaSignSlotRadialFormalEliminant.eliminant c i).coeff s).coeff t).coeff r).coeff v).natAbs ≤
      2 ^ FormulaSignSlotRadialEliminantFormalMass.budget q := by
  cases hc
  have HI : FormulaSignSlotRadialEliminantInput.coordinate q = i := Fin.ext hi
  rw [← HI]
  exact FormulaSignSlotRadialEliminantFormalMass.nested_abs q s t r v

private theorem coordinate_abs (c : List Bool) (i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c))
    (s t r : ℕ) (v : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) →₀ ℕ) :
    (((((FormulaSignSlotRadialFormalEliminant.eliminant
      (FormulaSignSlotRadialCenterValueLayout.original c) i).coeff s).coeff t).coeff r).coeff v).natAbs ≤
        2 ^ coordinateBudget c := by
  have HI : i.val < N (FormulaSignSlotRadialCenterValueLayout.original c) +
      d (FormulaSignSlotRadialCenterValueLayout.original c) + 1 := i.isLt
  have H := nested_at (FormulaSignSlotRadialCoordinatePacket.packet
    (FormulaSignSlotRadialCenterValueLayout.original c) i.val) _
    (FormulaSignSlotRadialCoordinatePacket.root _ i.val) i
    (by rw [FormulaSignSlotRadialCoordinatePacket.selected, Nat.min_eq_left (by omega)]) s t r v
  exact H.trans_eq (congrArg (fun b : ℕ => 2 ^ b) (budget_coordinate c i.val))

private theorem one_coefficient_at {A : ℕ} (p : Polynomial (MvPolynomial (Fin A) ℤ))
    (e : Fin (A + 1) →₀ ℕ) : (TriplePolynomialParameterFlatten.one p).coeff e =
      (p.coeff (e 0)).coeff e.tail := by
  simpa only [Finsupp.cons_tail] using TriplePolynomialParameterFlatten.one_coefficient p (e 0) e.tail

private theorem coordinate_mass (c : List Bool) (i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c)) (j : ℕ) :
    MvMass.mass (TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialCenterValueFamily.input (FormulaSignSlotRadialCenterValueLayout.original c)
        (fun k => FormulaSignSlotRadialCenterValueLayout.tau c k.val)
        (fun k => FormulaSignSlotRadialCenterValueLayout.degree c k.val) i).coeff j)) ≤ 2 ^ rowBudget c := by
  apply (PhysicalCriticalMassBudget.coefficient_box (FormulaSignSlotRadialCenterValuePacking.arity c)
      (FormulaSignSlotRadialCenterValuePacking.width c) (coordinateBudget c) _ ?_ ?_).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · intro e he k
    exact ((MvPolynomial.monomial_le_degreeOf k he).trans (MvPolynomial.degreeOf_le_totalDegree _ k)).trans_lt
      ((FormulaSignSlotRadialCenterValueBounds.input_degree _ _ _ i j).trans_lt
        (FormulaSignSlotRadialCenterValuePacking.input_fit c))
  · intro e
    have HC := one_coefficient_at
      ((FormulaSignSlotRadialCenterValueFamily.input (FormulaSignSlotRadialCenterValueLayout.original c)
        (fun k => FormulaSignSlotRadialCenterValueLayout.tau c k.val)
        (fun k => FormulaSignSlotRadialCenterValueLayout.degree c k.val) i).coeff j) e
    apply (congrArg Int.natAbs HC).le.trans
    rw [FormulaSignSlotRadialCenterValueFamily.input,
      FormulaSignSlotRadialCenterSquarefreeSelection.truncate_coefficient]
    split_ifs
    · exact coordinate_abs c i _ j (e 0) e.tail
    · simp

private theorem test_abs (c : List Bool) (e : Fin (FormulaSignSlotRadialCenterValueLayout.arity c) →₀ ℕ)
    (r : ℕ) (v : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) →₀ ℕ) :
    ((((FormulaSignSlotRadialFormalCenter.polynomial
      (FormulaSignSlotRadialCenterValueLayout.original c)).coeff e).coeff r).coeff v).natAbs ≤ 2 ^ testBudget c := by
  have H := MvMass.coeff_le (FormulaSignSlotRadialFormalInput.polynomial
    (FormulaSignSlotRadialCenterValueLayout.original c))
    (FormulaSignSlotRadialEliminantSource.exponent _ e r v)
  have HE := FormulaSignSlotRadialEliminantSource.coefficient _
    (FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueLayout.original c)) e r v
  rw [FormulaSignSlotRadialEliminantSource.flatten_eq] at HE
  exact ((congrArg Int.natAbs HE).symm.le.trans H).trans
    (FormulaSignSlotRadialEliminantScalarMass.source_mass _)

private theorem test_mass (c : List Bool) (e : Fin (FormulaSignSlotRadialCenterValueLayout.arity c) →₀ ℕ) :
    MvMass.mass (TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueLayout.original c)).coeff e)) ≤
        2 ^ rowBudget c := by
  apply (PhysicalCriticalMassBudget.coefficient_box (FormulaSignSlotRadialCenterValuePacking.arity c)
      (FormulaSignSlotRadialCenterValuePacking.width c) (testBudget c) _ ?_ ?_).trans
    (Nat.pow_le_pow_right (by decide) (by unfold rowBudget; omega))
  · intro f hf i
    exact ((MvPolynomial.monomial_le_degreeOf i hf).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      ((FormulaSignSlotRadialCenterValueBounds.test_degree _ e).trans_lt
        (FormulaSignSlotRadialCenterValueNativeFamily.test_fit c))
  · intro f
    exact (congrArg Int.natAbs (one_coefficient_at _ f)).le.trans (test_abs c e (f 0) f.tail)

private theorem original_mass (c : List Bool)
    (i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c + 1))
    (u : Fin (FormulaSignSlotRadialCenterValueLayout.arity c) →₀ ℕ) :
    coefficientMass ((FormulaSignSlotRadialCenterValueNativeFamily.family.affine.original c i).coeff u) ≤
      2 ^ rowBudget c := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change coefficientMass (((FormulaSignSlotRadialFormalCenter.polynomial
      (FormulaSignSlotRadialCenterValueLayout.original c)).map
        (FormulaSignSlotRadialCenterValuePacking.parameterMap c)).coeff u) ≤ _
    rw [MvPolynomial.coeff_map]
    exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (test_mass c u)
  · change coefficientMass (((FormulaSignSlotRadialCenterValueNativeFamily.family.coordinate c j).toMvPolynomial j).coeff u) ≤ _
    rw [DiagonalParameterBits.coefficient]
    split_ifs
    · change coefficientMass ((FormulaSignSlotRadialCenterValueCoordinateReader.packed
        (pair c (BinaryNatCode.encode j.val))).coeff _) ≤ _
      rw [FormulaSignSlotRadialCenterValueCoordinateReader.packed_packet, Polynomial.coeff_map]
      exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (coordinate_mass c j _)
    · simp

theorem packed_mass (c : List Bool) : NestedMass.mass
    (FormulaSignSlotRadialCenterValuePacking.polynomial c) ≤
      2 ^ ProjectiveValueGram.massExponent (FormulaSignSlotRadialCenterValueLayout.arity c)
        (FormulaSignSlotRadialCenterValueLayout.width c) (rowBudget c) := by
  rw [← FormulaSignSlotRadialCenterValueNativeFamily.annihilator_eq]
  exact AffineValueGramBits.Family.mass_le _ rowBudget original_mass c

theorem mass (c : List Bool) (j : ℕ) :
    MvMass.mass (TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialCenterValuePacking.source c).coeff j)) ≤ 2 ^ budget c := by
  apply FixedWidthTarskiMass.mass_le_pow
  · intro e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      ((FormulaSignSlotRadialCenterValuePacking.source_degree c j).trans_lt
        (FormulaSignSlotRadialCenterValuePacking.degree_fit c))
  · have H := (NestedMass.coeff_le (FormulaSignSlotRadialCenterValuePacking.polynomial c) j).trans (packed_mass c)
    rw [FormulaSignSlotRadialCenterValuePacking.polynomial, Polynomial.coeff_map] at H
    exact H

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueMass
