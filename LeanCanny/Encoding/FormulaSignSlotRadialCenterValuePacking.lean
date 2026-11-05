/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueBounds
public import LeanCanny.Algebra.RelativeAffineGridValueParameterMap
/-! # Original-only joint parameter packing for the literal value certificate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValuePacking
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def inputBound (c : List Bool) := FormulaSignSlotRadialCenterValueSelection.bound
  (FormulaSignSlotRadialCenterValueLayout.original c)
noncomputable def arity (c : List Bool) := d (FormulaSignSlotRadialCenterValueLayout.original c) + 1
noncomputable def dimension (c : List Bool) := RelativeProjectiveValueGram.dimension
  (FormulaSignSlotRadialCenterValueLayout.arity c) (FormulaSignSlotRadialCenterValueLayout.width c)
noncomputable def degree (c : List Bool) := dimension c * (inputBound c + 2)
noncomputable def width (c : List Bool) := (inputBound c).size + (degree c).size
noncomputable def box (c : List Bool) := FixedWidthPolynomial.count (arity c) (width c)

def originalPacket (c : List Bool) := FormulaSignSlotRadialCoordinatePacket.writer
  (pair (FormulaSignSlotRadialCenterValueLayout.original c) (BinaryNatCode.encode 0))
theorem originalPacket_FP : originalPacket ∈ FP := mem_FP_comp
  (mem_FP_pair FormulaSignSlotRadialCenterValueLayout.original_FP (constFn_mem_FP _))
  FormulaSignSlotRadialCoordinatePacket.writer_FP

theorem inputBound_binary : BinaryFn inputBound := by
  have H : BinaryFn (fun c => FormulaSignSlotRadialEliminantPacked.resultDegree (originalPacket c)) :=
    FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp originalPacket_FP
  exact H.of_eq (fun c => by rw [originalPacket, FormulaSignSlotRadialCoordinatePacket.writer_packet]; rfl)
theorem arity_unary : UnaryFn arity :=
  (FormulaSignSlotSource.dimension_unary.comp FormulaSignSlotRadialCenterValueLayout.original_FP).add (UnaryFn.const 1)
theorem dimension_binary : BinaryFn dimension := by
  have HE := (FormulaSignSlotRadialCenterValueLayout.arity_unary.add (UnaryFn.const 1)).mul
    FormulaSignSlotRadialCenterValueLayout.width_unary
  have HC : BinaryFn (fun c => FixedWidthPolynomial.count
      (FormulaSignSlotRadialCenterValueLayout.arity c + 1) (FormulaSignSlotRadialCenterValueLayout.width c)) :=
    ((BinaryFn.const 2).powUnary HE).of_eq (fun c => by
      simp only [FixedWidthPolynomial.count, ← pow_mul, Nat.mul_comm])
  exact (BinaryFn.ofUnary (FormulaSignSlotRadialCenterValueLayout.arity_unary.add (UnaryFn.const 3))).mul HC
theorem degree_binary : BinaryFn degree := dimension_binary.mul (inputBound_binary.add (BinaryFn.const 2))
theorem width_unary : UnaryFn width :=
  ((UnaryFn.length inputBound_binary.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)).add
    ((UnaryFn.length degree_binary.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _))
theorem box_binary : BinaryFn box :=
  ((BinaryFn.const 2).powUnary (arity_unary.mul width_unary)).of_eq (fun c => by
    simp only [box, FixedWidthPolynomial.count, ← pow_mul, Nat.mul_comm])

theorem input_fit (c : List Bool) : inputBound c < 2 ^ width c :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
theorem degree_fit (c : List Bool) : degree c < 2 ^ width c :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

noncomputable def parameterMap (c : List Bool) : FormulaSignSlotRadialFormalCenter.Radius
    (FormulaSignSlotRadialCenterValueLayout.original c) →+* Polynomial ℤ :=
  (FixedWidthKronecker.encode (arity c) (width c)).comp TriplePolynomialParameterFlatten.one
noncomputable def source (c : List Bool) := FormulaSignSlotRadialCenterValueFamily.polynomial
  (FormulaSignSlotRadialCenterValueLayout.original c)
    (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
    (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val)
noncomputable def polynomial (c : List Bool) : Polynomial (Polynomial ℤ) := (source c).map (parameterMap c)

theorem spatial_width (c : List Bool) : FormulaSignSlotRadialCenterValueLayout.width c =
    RelativeAffineGridValueGram.width
      (fun i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c) => FormulaSignSlotRadialCenterValueLayout.degree c i.val)
      (FormulaSignSlotRadialCenterValueLayout.testDegree c) := by
  exact congrArg Nat.size (FormulaSignSlotRadialCenterValueLayout.level_eq c)

theorem source_degree (c : List Bool) (j : ℕ) :
    (TriplePolynomialParameterFlatten.one ((source c).coeff j)).totalDegree ≤ degree c := by
  have H := FormulaSignSlotRadialCenterValueBounds.polynomial_degree
    (FormulaSignSlotRadialCenterValueLayout.original c)
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val) j
  simpa only [source, degree, dimension, inputBound, spatial_width,
    FormulaSignSlotRadialCenterValueLayout.arity, FormulaSignSlotRadialFormalInput.spatial,
    FormulaSignSlotRadialCenterValueLayout.testDegree] using H

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValuePacking
