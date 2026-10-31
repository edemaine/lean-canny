/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceChildPowerRows
public import LeanCanny.Encoding.FlatAffinePowerRootTransport

/-! # Powered child roots return to the single trace family -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] objective levels depth append seedCoordinate

def childProjection (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    Fin (FlatAffineFullSourcePositive.count (inputs P d old level) (append midpoint q)) →
      Fin (FlatAffineFullSourcePositive.count
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :=
  Fin.cast (congrArg (fun F : FlatAffineFullSourceTower.Inputs => FlatAffineFullSourcePositive.count F q)
    (extendedInputs_eq_context midpoint P d old level)).symm

theorem childProjection_val (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count (inputs P d old level) (append midpoint q))) :
    (childProjection midpoint P d old level q i).val = i.val := rfl

noncomputable def powerRoot (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : FlatAffinePowerRootTransport.Roots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    FlatAffinePowerRootTransport.Roots (inputs P d old level) (append midpoint q) :=
  FlatAffinePowerRootTransport.context (inputs P d old level) (append midpoint) q
    (FlatAffinePowerRootTransport.transport (extendedInputs midpoint P d old level)
      (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint))
      (extendedInputs_eq_context midpoint P d old level) q
      ⟨x.val, fun i => (congrArg (fun s => (s i).eval₂ (Int.castRingHom ℝ) x.val)
        (extended_power_system midpoint P d old level q hv)).trans (x.property i)⟩)

attribute [local irreducible] powerRoot

theorem powerRoot_val (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : FlatAffinePowerRootTransport.Roots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    (powerRoot midpoint P d old level q hv x).val = x.val ∘ childProjection midpoint P d old level q := by
  unfold powerRoot
  exact (FlatAffinePowerRootTransport.context_val (inputs P d old level) (append midpoint) q _).trans
    (FlatAffinePowerRootTransport.transport_val (extendedInputs midpoint P d old level)
      (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint))
      (extendedInputs_eq_context midpoint P d old level) q _)

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
