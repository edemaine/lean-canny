/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourcePositiveCoefficient
public import LeanCanny.Encoding.FlatAffineFullSourceContext
public import LeanCanny.Algebra.AffineCoordinateRowsSpace

/-! # Native homogenized rows for complete affine tower elimination -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourcePositiveRows
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs degree)
open FlatAffineFullSourcePositive (count system)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffineFullSourceTower.system

noncomputable def frame (F : Inputs) : Inputs := FlatAffineFullSourceContext.comp F pairFst

theorem system_comp (F : Inputs) (f : List Bool → List Bool) (q : List Bool) (i : Fin (count F (f q))) :
    system (FlatAffineFullSourceContext.comp F f) q i = system F (f q) i := by
  unfold system
  have hs : FlatAffineFullSourceTower.system (FlatAffineFullSourceContext.comp F f) q = FlatAffineFullSourceTower.system F (f q) :=
    funext (FlatAffineFullSourceContext.system_comp F f q)
  rw [hs]

theorem frame_system (F : Inputs) (q : List Bool) (i : Fin (count F (pairFst q))) :
    system (frame F) q i = system F (pairFst q) i := system_comp F pairFst q i

theorem integer_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (row : (c : List Bool) → Fin (count F c)) (hr : UnaryFn (fun c => (row c).val))
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (HomogenizationPolynomialBits.integerValue (count F) W (fun c => system F c (row c)) modulus) := by
  let row' : (q : List Bool) → Fin (count (frame F) q) := fun q => row (pairFst q)
  have E := FlatAffineFullSourcePositiveCoefficient.evaluator (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) row' (hr.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  refine E.congr (funext fun q => ?_)
  have H := FlatAffineFullSourcePositiveCoefficient.packet (frame F) (W ∘ pairFst) row' pairSnd (modulus ∘ pairFst) q
  rw [frame_system] at H
  dsimp +instances only [HomogenizationPolynomialBits.integerValue, Function.comp_def, count,
    FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity,
    frame, FlatAffineFullSourceContext.comp, BoundedFullWriter.Readers.comp] at H ⊢
  exact H

theorem evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (hwpos : ∀ c, 0 < W c)
    (coordinate : (c : List Bool) → Fin (count F c)) (hc : UnaryFn (fun c => (coordinate c).val))
    (row : (c : List Bool) → Fin (count F c + 1)) (hr : UnaryFn (fun c => (row c).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (AffineCoordinateRowsBits.value (count F) W (degree F) (system F) coordinate row parameter modulus) :=
  AffineCoordinateRowsBits.evaluator (FlatAffineFullSourcePositive.count_unary h) hW
    (FlatAffineFullSourceTower.degree_binary h) (FlatAffineFullSourcePositive.count_pos F) hwpos (system F) coordinate hc row hr hk hm
    (integer_evaluator h hW (AffineCoordinateRowsBits.tailRow (count F) (FlatAffineFullSourcePositive.count_pos F) row)
      (AffineCoordinateRowsBits.tailRow_unary (FlatAffineFullSourcePositive.count_unary h)
        (FlatAffineFullSourcePositive.count_pos F) row hr) hm)

end LeanCanny.Encoding.FlatAffineFullSourcePositiveRows
