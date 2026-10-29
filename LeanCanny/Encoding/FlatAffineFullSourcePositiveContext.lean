/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourcePositiveCoordinate
public import LeanCanny.Encoding.FlatAffineFullSourcePositiveRows

/-! # Source contexts for flat coordinate equations

The complete source, directions, and stage metadata move together. The
positive system and its coordinate equation are the existing objects at the
transformed source input; the elimination is not recomputed on a truncated
context or on separately supplied ancestral coefficients.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourcePositiveContext
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffineFullSourcePositive.system FlatAffineFullSourceTower.degree

theorem count_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourcePositive.count (FlatAffineFullSourceContext.comp F f) u = FlatAffineFullSourcePositive.count F (f u) := rfl

theorem level_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourcePositiveCoordinate.level (FlatAffineFullSourceContext.comp F f) u =
      FlatAffineFullSourcePositiveCoordinate.level F (f u) := by
  unfold FlatAffineFullSourcePositiveCoordinate.level
  rw [FlatAffineFullSourceContext.degree_comp, count_comp]

theorem width_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourcePositiveCoordinate.width (FlatAffineFullSourceContext.comp F f) u =
      FlatAffineFullSourcePositiveCoordinate.width F (f u) := congrArg Nat.size (level_comp F f u)

theorem polynomial_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count F (f u))) :
    FlatAffineFullSourcePositiveCoordinate.polynomial (FlatAffineFullSourceContext.comp F f) u i =
      FlatAffineFullSourcePositiveCoordinate.polynomial F (f u) i := by
  unfold FlatAffineFullSourcePositiveCoordinate.polynomial
  have hs : FlatAffineFullSourcePositive.system (FlatAffineFullSourceContext.comp F f) u = FlatAffineFullSourcePositive.system F (f u) :=
    funext (FlatAffineFullSourcePositiveRows.system_comp F f u)
  rw [hs, FlatAffineFullSourceContext.degree_comp, width_comp]
  dsimp only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity,
    FlatAffineFullSourceContext.comp, BoundedFullWriter.Readers.comp, Function.comp_def]

end LeanCanny.Encoding.FlatAffineFullSourcePositiveContext
