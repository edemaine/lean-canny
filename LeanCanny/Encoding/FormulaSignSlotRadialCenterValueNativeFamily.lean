/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoordinateReader
public import LeanCanny.Algebra.IntegerGridValueGramSpace
/-! # The actual integer value-reader family after joint parameter packing -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueNativeFamily
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def family : IntegerGridValueGramBits.Family where
  arity := FormulaSignSlotRadialCenterValueLayout.arity
  width := FormulaSignSlotRadialCenterValueLayout.width
  degree := FormulaSignSlotRadialCenterValueLayout.degree
  testDegree := FormulaSignSlotRadialCenterValueLayout.testDegree
  coordinate := FormulaSignSlotRadialCenterValueCoordinateReader.coordinate
  test c := (FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueLayout.original c)).map
    (FormulaSignSlotRadialCenterValuePacking.parameterMap c)

theorem controls : family.affine.homogeneous.layout.Controls := by
  refine ⟨FormulaSignSlotRadialCenterValueLayout.arity_unary.add (UnaryFn.const 1),
    FormulaSignSlotRadialCenterValueLayout.width_unary, ?_, FormulaSignSlotRadialCenterValueLayout.controls.degree⟩
  exact FormulaSignSlotRadialCenterValueLayout.level_binary.of_eq FormulaSignSlotRadialCenterValueLayout.level_eq

private theorem encoded_degree (A W : ℕ) (p : MvPolynomial (Fin A) ℤ) (h : p.totalDegree < 2 ^ W) :
    (FixedWidthKronecker.encode A W p).natDegree ≤ FixedWidthPolynomial.count A W := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact FixedWidthKronecker.coefficient_of_ge A W p (fun e he i =>
    ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt h) k hk.le

theorem test_fit (c : List Bool) : 2 < 2 ^ FormulaSignSlotRadialCenterValuePacking.width c := by
  have HD : 0 < FormulaSignSlotRadialCenterValuePacking.dimension c := by
    unfold FormulaSignSlotRadialCenterValuePacking.dimension RelativeProjectiveValueGram.dimension FixedWidthPolynomial.count
    exact Nat.mul_pos (by omega) (Nat.pow_pos (Nat.two_pow_pos _))
  have HE : 2 ≤ FormulaSignSlotRadialCenterValuePacking.degree c := by
    unfold FormulaSignSlotRadialCenterValuePacking.degree
    nlinarith [Nat.zero_le (FormulaSignSlotRadialCenterValuePacking.inputBound c)]
  exact HE.trans_lt (FormulaSignSlotRadialCenterValuePacking.degree_fit c)

theorem coordinate_inner_degree (c : List Bool) (i : Fin (family.arity c)) (k : ℕ) :
    ((family.coordinate c i).coeff k).natDegree ≤ FormulaSignSlotRadialCenterValuePacking.box c := by
  change ((FormulaSignSlotRadialCenterValueCoordinateReader.packed (pair c (BinaryNatCode.encode i.val))).coeff k).natDegree ≤ _
  rw [FormulaSignSlotRadialCenterValueCoordinateReader.packed_packet, Polynomial.coeff_map]
  change (FixedWidthKronecker.encode _ _ _).natDegree ≤ _
  apply encoded_degree
  exact (FormulaSignSlotRadialCenterValueBounds.input_degree _ _ _ i k).trans_lt
    (FormulaSignSlotRadialCenterValuePacking.input_fit c)

theorem test_inner_degree (c : List Bool) (u : Fin (family.arity c) →₀ ℕ) :
    ((family.test c).coeff u).natDegree ≤ FormulaSignSlotRadialCenterValuePacking.box c := by
  change (((FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueLayout.original c)).map
    (FormulaSignSlotRadialCenterValuePacking.parameterMap c)).coeff u).natDegree ≤ _
  rw [MvPolynomial.coeff_map]
  change (FixedWidthKronecker.encode _ _ _).natDegree ≤ _
  exact encoded_degree _ _ _ ((FormulaSignSlotRadialCenterValueBounds.test_degree _ u).trans_lt (test_fit c))

private theorem native_annihilator (F : IntegerGridValueGramBits.Family) (c : List Bool) :
    F.affine.homogeneous.annihilator c = RelativeProjectiveValueGram.annihilator
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows (F.coordinate c))
        (fun i => F.degree c i.val)) (RelativeAffineGridValueGram.test (F.test c) (F.testDegree c))
      (fun i => F.degree c i.val) (F.testDegree c) (F.width c) := rfl

theorem annihilator_eq (c : List Bool) : family.affine.homogeneous.annihilator c =
    FormulaSignSlotRadialCenterValuePacking.polynomial c := by
  have HC : family.coordinate c = fun i =>
      (FormulaSignSlotRadialCenterValueFamily.input (FormulaSignSlotRadialCenterValueLayout.original c)
        (fun j => FormulaSignSlotRadialCenterValueLayout.tau c j.val)
        (fun j => FormulaSignSlotRadialCenterValueLayout.degree c j.val) i).map
          (FormulaSignSlotRadialCenterValuePacking.parameterMap c) := by
    funext i
    exact FormulaSignSlotRadialCenterValueCoordinateReader.packed_packet c i
  rw [native_annihilator, FormulaSignSlotRadialCenterValuePacking.polynomial,
    FormulaSignSlotRadialCenterValuePacking.source, FormulaSignSlotRadialCenterValueFamily.polynomial,
    RelativeAffineGridValueParameterMap.annihilator, ← HC]
  unfold RelativeAffineGridValueGram.annihilator
  dsimp only [family]
  have HW : RelativeAffineGridValueGram.width
      (fun i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c) => FormulaSignSlotRadialCenterValueLayout.degree c i.val)
      (FormulaSignSlotCenteredRadialLimits.degreeBudget (FormulaSignSlotRadialCenterValueLayout.original c) + 1) =
        FormulaSignSlotRadialCenterValueLayout.width c := (FormulaSignSlotRadialCenterValuePacking.spatial_width c).symm
  erw [HW]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueNativeFamily
