/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProducer
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # The actual regularized radial graph supplies the mixed sampler source

The integer lower polynomial and leading scalar are literal producer fields.
The source degree and one scalar cap depend on the original equation, even
when the binary radius is varied.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialSpatialSource
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra MvPolynomial
open FormulaSignSlotRadialProducer
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

noncomputable def spatial (q : List Bool) : IntegralMixedHistory.SpatialSource (readers.dim q+3) where
  low := rename (BoundedFullGeometry.inputIndex (readers.dim q+3))
    (IntegerRegularSource.lower
      (BoundedRegularSource.lower (BoundedFullWriter.original readers q) (BoundedFullWriter.size readers q)
        (BoundedFullWriter.size readers q) (radius q)) (BoundedFullWriter.degree readers q)
      (BoundedRegularSource.sourceMassExponent (readers.dim q) (BoundedFullWriter.size readers q)
        (BoundedFullWriter.size readers q) (radius q)))
  leading := IntegerRegularSource.leading (readers.dim q+3) 1 (BoundedFullWriter.degree readers q)
    (BoundedRegularSource.sourceMassExponent (readers.dim q) (BoundedFullWriter.size readers q)
      (BoundedFullWriter.size readers q) (radius q))
  degree := BoundedFullWriter.degree readers q
  degree_two := by
    have H := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size readers q)
    exact H
  low_degree := (totalDegree_rename_le _ _).trans_lt (IntegerRegularSource.lower_degree _ _ _
    (BoundedRegularSource.lower_degree _ _ _ _ (BoundedFullWriter.original_degree readers q)))
  leading_ne_zero := IntegerRegularSource.leading_ne_zero 1 _ _ one_ne_zero

theorem polynomial_eq (q : List Bool) : BoundedFullCriticalSamples.polynomial readers q=
    FermatCriticalHomogenization.polynomial (spatial q).low (spatial q).leading (spatial q).degree :=
  BoundedFullGeometry.polynomial_eq _ _ _ _

theorem degree_eq (q : List Bool) : (spatial q).degree=
    BoundedZeroSource.powerDegree (FormulaSignSlotRadialEquation.budget (root q)) := by
  change BoundedZeroSource.powerDegree (BoundedFullWriter.size readers q)=_
  rw [FormulaSignSlotRadialProducer.size_eq]

theorem degree_same_root (q r : List Bool) (h : root q=root r) : (spatial q).degree=(spatial r).degree := by
  rw [degree_eq,degree_eq,h]

noncomputable def scalarWidth (q : List Bool) :=
  PurePowerReductionBounds.width (readers.dim q+4) (spatial q).degree * (readers.dim q+4)

theorem scalarWidth_unary : UnaryFn scalarWidth := by
  have HD := access.dim.add (UnaryFn.const 4)
  exact (PurePowerReductionBounds.width_unary HD FormulaSignSlotRadialProducer.degree_binary).mul HD

theorem scalar_cap (q : List Bool) :
    PurePowerReductionBounds.dimension (readers.dim q+4) (spatial q).degree=2^scalarWidth q := by
  simp only [PurePowerReductionBounds.dimension,FixedWidthPolynomial.count,← pow_mul]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialSpatialSource
