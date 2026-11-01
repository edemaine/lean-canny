/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalMatrix

/-! # Staged same-parent transport of the actual double-nilpotent system -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMappedSystemPull
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedValueDoubleSystem

theorem original (F : Family) (base : List Bool → List Bool) (q : List Bool)
    (i : Fin (F.ambient (base q) - (F.rule (base q)).critical.offset.val + 1)) :
    IntegralMixedVirtualOriginalRows.row (pull F base) q i = IntegralMixedVirtualOriginalRows.row F (base q) i := rfl

theorem coordinate (F : Family) (base : List Bool → List Bool) (q : List Bool)
    (i : Fin (F.ambient (base q) - (F.rule (base q)).critical.offset.val + 1)) :
    coordinates (pull F base) q i = coordinates F (base q) i := rfl

theorem system_eq (F : Family) (base : List Bool → List Bool) (q : List Bool)
    (i : Fin (F.ambient (base q) - (F.rule (base q)).critical.offset.val + 1))
    (j : Fin (F.ambient (base q) - (F.rule (base q)).critical.offset.val + 1 + 1)) :
    system (pull F base) q i j = system F (base q) i j := by
  have HC : coordinates (pull F base) q = coordinates F (base q) := funext (coordinate F base q)
  unfold system
  rw [HC, original F base q i]
  rfl

theorem mapped (F : Family) (base : List Bool → List Bool) (q : List Bool)
    (i : Fin (F.ambient (base q) - (F.rule (base q)).critical.offset.val + 1))
    (j : Fin (F.ambient (base q) - (F.rule (base q)).critical.offset.val + 1 + 1)) :
    mappedSystem (pull F base) q i j = mappedSystem F (base q) i j := by
  unfold mappedSystem
  rw [system_eq F base q i j]
  rfl

end LeanCanny.Algebra.IntegralMixedValueMappedSystemPull
