/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositiveCoordinate
public import LeanCanny.Encoding.FlatFullSourcePositiveRows

/-! # Source contexts for flat coordinate equations

The complete source, directions, and stage metadata move together. The
positive system and its coordinate equation are the existing objects at the
transformed source input; the elimination is not recomputed on a truncated
context or on separately supplied ancestral coefficients.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositiveContext
open LeanCanny.Algebra LeanCanny.Computation
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourcePositive.system FlatFullSourceTower.degree

theorem count_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatFullSourcePositive.count (FlatFullSourceContext.comp F f) u = FlatFullSourcePositive.count F (f u) := rfl

theorem level_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatFullSourcePositiveCoordinate.level (FlatFullSourceContext.comp F f) u =
      FlatFullSourcePositiveCoordinate.level F (f u) := by
  unfold FlatFullSourcePositiveCoordinate.level
  rw [FlatFullSourceContext.degree_comp, count_comp]

theorem width_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatFullSourcePositiveCoordinate.width (FlatFullSourceContext.comp F f) u =
      FlatFullSourcePositiveCoordinate.width F (f u) := congrArg Nat.size (level_comp F f u)

theorem polynomial_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (i : Fin (FlatFullSourcePositive.count F (f u))) :
    FlatFullSourcePositiveCoordinate.polynomial (FlatFullSourceContext.comp F f) u i =
      FlatFullSourcePositiveCoordinate.polynomial F (f u) i := by
  unfold FlatFullSourcePositiveCoordinate.polynomial
  have hs : FlatFullSourcePositive.system (FlatFullSourceContext.comp F f) u = FlatFullSourcePositive.system F (f u) :=
    funext (FlatFullSourcePositiveRows.system_comp F f u)
  rw [hs, FlatFullSourceContext.degree_comp, width_comp]
  dsimp only [FlatFullSourcePositive.count, FlatFullSourceTower.count, FlatFullSourceTower.arity,
    FlatFullSourceContext.comp, BoundedFullWriter.Readers.comp, Function.comp_def]

end LeanCanny.Encoding.FlatFullSourcePositiveContext
