/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Encoding.FlatAffineFullSourcePositiveCoordinateCoefficient
public import LeanCanny.Encoding.FlatAffineFullSourcePositiveContext

/-! # Complete affine towers instantiate the square sampling interface

Both canonical coefficient readers are constructed from the proved affine
row and coordinate-elimination programs. No additional coefficient-access
premise is required beyond the original source and record access certificate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSampleInput
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffineFullSourcePositive.system FlatAffineFullSourcePositiveCoordinate.polynomial

noncomputable def input (F : FlatAffineFullSourceTower.Inputs) : SquareSampleInput.Inputs where
  count := FlatAffineFullSourcePositive.count F
  degree := FlatAffineFullSourceTower.degree F
  mass := FlatAffineFullSourceTower.mass F
  system := FlatAffineFullSourcePositive.system F
  count_pos := FlatAffineFullSourcePositive.count_pos F
  degree_pos := FlatAffineFullSourceTower.degree_pos F
  system_degree := FlatAffineFullSourcePositive.polynomial_degree F
  system_mass := FlatAffineFullSourcePositive.polynomial_mass F
  annihilator := FlatAffineFullSourcePositiveCoordinate.polynomial F
  annDegree := FlatAffineFullSourcePositiveCoordinate.matrixCount F
  annHeight := FlatAffineFullSourcePositiveCoordinate.coefficientBits F
  ann_nonzero := FlatAffineFullSourcePositiveCoordinate.ne_zero F
  ann_degree := FlatAffineFullSourcePositiveCoordinate.polynomial_degree F
  ann_height := FlatAffineFullSourcePositiveCoordinate.polynomial_coefficient_bits F
  ann_root := FlatAffineFullSourcePositiveCoordinate.eval_regular_root F

noncomputable def frame (F : FlatAffineFullSourceTower.Inputs) := FlatAffineFullSourceContext.comp F SquareSampleInput.source

noncomputable def row (F : FlatAffineFullSourceTower.Inputs) (q : List Bool) :
    Fin (FlatAffineFullSourcePositive.count (frame F) q) :=
  SquareSampleInput.selected (input F) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem row_unary {F : FlatAffineFullSourceTower.Inputs} (h : F.Access) : UnaryFn (fun q => (row F q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    (((FlatAffineFullSourcePositive.count_unary h).comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

theorem row_evaluator {F : FlatAffineFullSourceTower.Inputs} (h : F.Access) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input F)) := by
  have E := FlatAffineFullSourcePositiveCoefficient.evaluator
    (FlatAffineFullSourceContext.access h SquareSampleInput.source_FP)
    (UnaryFn.length SquareSampleInput.widthWord_FP) (row F) (row_unary h)
    SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  refine E.congr (funext fun q => ?_)
  have H := FlatAffineFullSourcePositiveCoefficient.packet (frame F)
    (fun q => (SquareSampleInput.widthWord q).length) (row F) SquareSampleInput.rankWord SquareSampleInput.modulusWord q
  have hp := FlatAffineFullSourcePositiveRows.system_comp F SquareSampleInput.source q (row F q)
  change FlatAffineFullSourcePositive.system (frame F) q (row F q) = _ at hp
  rw [hp] at H
  dsimp +instances only [SquareSampleInput.rowCoefficient, SquareSampleInput.rowValue, input, frame,
    FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth,
    FlatAffineFullSourceTower.arity, FlatAffineFullSourceContext.comp, BoundedFullWriter.Readers.comp] at H ⊢
  exact H

theorem ann_evaluator {F : FlatAffineFullSourceTower.Inputs} (h : F.Access) :
    SpaceFunction (SquareSampleInput.annCoefficient (input F)) := by
  have E := FlatAffineFullSourcePositiveCoordinateCoefficient.evaluator
    (FlatAffineFullSourceContext.access h SquareSampleInput.source_FP) (row F) (row_unary h)
  let prepare (q : List Bool) := pair (pair q (SquareSampleInput.modulusWord q))
    (BinaryNat.normalize (SquareSampleInput.rankWord q))
  have hprepare : prepare ∈ FP := mem_FP_pair (mem_FP_pair id_mem_FP SquareSampleInput.modulusWord_FP)
    (mem_FP_comp SquareSampleInput.rankWord_FP BinaryNat.normalize_mem_FP)
  refine (E.precompose prepare hprepare).congr (funext fun q => ?_)
  change FlatAffineFullSourcePositiveCoordinateCoefficient.value (frame F) (row F) (prepare q) = _
  simp only [prepare, BinaryNat.normalize_eq_bits]
  have H := FlatAffineFullSourcePositiveCoordinateCoefficient.value_packet (frame F) (row F) q
    (SquareSampleInput.modulusWord q) (Nat.fromBitsLE (SquareSampleInput.rankWord q))
  have hp : FlatAffineFullSourcePositiveCoordinate.polynomial (frame F) q (row F q) =
      FlatAffineFullSourcePositiveCoordinate.polynomial F (SquareSampleInput.source q) (row F q) :=
    FlatAffineFullSourcePositiveContext.polynomial_comp F SquareSampleInput.source q (row F q)
  rw [hp] at H
  dsimp +instances only [SquareSampleInput.annCoefficient, SquareSampleInput.annValue, input, row, frame,
    FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth,
    FlatAffineFullSourceTower.arity, FlatAffineFullSourceContext.comp, BoundedFullWriter.Readers.comp] at H ⊢
  exact H

theorem access {F : FlatAffineFullSourceTower.Inputs} (h : F.Access) : (input F).Access :=
  ⟨FlatAffineFullSourcePositive.count_unary h, FlatAffineFullSourceTower.degree_binary h,
    FlatAffineFullSourceTower.mass_binary h, FlatAffineFullSourcePositiveCoordinate.matrixCount_binary h,
    FlatAffineFullSourcePositiveCoordinate.coefficientBits_binary h, row_evaluator h, ann_evaluator h⟩

end LeanCanny.Encoding.FlatAffineSampleInput
