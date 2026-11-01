/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeHeight
public import LeanCanny.Algebra.IntegralMixedVirtualNativeHeight
/-! # The actual scalar-height callbacks use the literal natural-index matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHeightNaturalBridge
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical (P : Parameters) (F : IntegralMixedPhysicalCriticalBits.Family) (q : List Bool)
    (i : Fin (F.ambient (IntegralMixedPhysicalTaskBits.saved P q) + 1)) (hi : get P .slot8 q = i.val) :
    IntegralMixedPhysicalNativeLowerBits.height P F q = residueBits
      (IntegralMixedHeightNaturalEntries.physical (F.state (IntegralMixedPhysicalTaskBits.saved P q))
        (F.birth_bound (IntegralMixedPhysicalTaskBits.saved P q)) (F.rule (IntegralMixedPhysicalTaskBits.saved P q)) i
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [IntegralMixedPhysicalNativeLowerBits.height_eq, hi]
  rfl

theorem virtual (P : Parameters) (F : IntegralMixedCutSource.Family) (q : List Bool)
    (i : Fin (F.ambient (IntegralMixedVirtualTaskBits.saved P q) + 1)) (hi : get P .slot8 q = i.val) :
    IntegralMixedVirtualNativeLowerBits.height P F q = residueBits
      (IntegralMixedHeightNaturalEntries.virtual (F.state (IntegralMixedVirtualTaskBits.saved P q))
        (F.birth_bound (IntegralMixedVirtualTaskBits.saved P q)) (F.rule (IntegralMixedVirtualTaskBits.saved P q)) i
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [IntegralMixedVirtualNativeLowerBits.height_eq, hi]
  rfl

end LeanCanny.Algebra.IntegralMixedFullHeightNaturalBridge
