/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceChildSteps
public import LeanCanny.Encoding.FlatAffineFullSourceContext

/-! # Returning an extended history to the same native input family -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

theorem readers_append (P : BoundedFullWriter.Readers) (midpoint : Bool) :
    (readers P).comp (append midpoint) = readers P := by
  have H : base ∘ append midpoint = base := funext (base_append midpoint)
  unfold readers BoundedFullWriter.Readers.comp
  simp only [Function.comp_assoc, H]

theorem depth_append_function (d : List Bool → ℕ) (midpoint : Bool) :
    depth d ∘ append midpoint = CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) :=
  funext (depth_append midpoint d)

noncomputable def extendedInputs (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffineFullSourceTower.Inputs :=
  CoordinateDoubleAffinePrefix.inputs (readers P) (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (objective d old ∘ FlatAffineFullSourceContext.query (append midpoint))
    (levels P d old level ∘ FlatAffineFullSourceContext.levelQuery (append midpoint))

attribute [local irreducible] objective levels depth append

theorem extendedInputs_eq_context (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) :
    extendedInputs midpoint P d old level = FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint) := by
  unfold extendedInputs inputs CoordinateDoubleAffinePrefix.inputs FlatAffineFullSourceContext.comp
  simp only [readers_append, depth_append_function]
  congr 1
  · funext q
    simp only [Function.comp_apply, FlatAffineFullSourceContext.query, readers, BoundedFullWriter.Readers.comp,
      LeanCanny.pairFst_pair, base_append]
  · funext q
    simp only [Function.comp_apply, CoordinateAffinePrefix.levels, CoordinateAffinePrefix.setFlags, CoordinateAffinePrefix.cut,
      FlatAffineFullSourceContext.levelQuery,
      FlatAffineFullSourceContext.query, readers, BoundedFullWriter.Readers.comp,
      LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, base_append]

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
