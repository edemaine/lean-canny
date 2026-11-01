/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightTableMatrix
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
/-! # Actual normalized old-basis rows in physical and nilpotent height queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightIndexBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedOldHeightBits (bankFamily oldRank)
set_option backward.isDefEq.respectTransparency false

theorem row_physical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (hx : get P .slot15 q = 1) :
    IntegralMixedHeightTableMatrixBits.row P D q = IntegralMixedHeightNaturalEntries.index
      ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .row q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldRow P q = get P .row q % oldRank P D q
  rw [IntegralMixedHeightTableQueryBits.oldRow, ite_eq_left hx, IntegralMixedOldHeightBits.oldRank_eq]

theorem col_physical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (hx : get P .slot15 q = 1) :
    IntegralMixedHeightTableMatrixBits.col P D q = IntegralMixedHeightNaturalEntries.index
      ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .col q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldCol P q = get P .col q % oldRank P D q
  rw [IntegralMixedHeightTableQueryBits.oldCol, ite_eq_left hx, IntegralMixedOldHeightBits.oldRank_eq]

theorem row_virtual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (hx : get P .slot15 q ≠ 1) :
    IntegralMixedHeightTableMatrixBits.row P D q = IntegralMixedHeightNaturalEntries.oldIndex
      ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .row q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldRow P q =
    (get P .row q / 2 ^ ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q))) % oldRank P D q
  rw [IntegralMixedHeightTableQueryBits.oldRow, ite_eq_right hx, IntegralMixedOldHeightBits.oldRank_eq,
    (IntegralMixedFullHistoryFamilyBits.geometry P D).width q]
  rfl

theorem col_virtual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (hx : get P .slot15 q ≠ 1) :
    IntegralMixedHeightTableMatrixBits.col P D q = IntegralMixedHeightNaturalEntries.oldIndex
      ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .col q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldCol P q =
    (get P .col q / 2 ^ ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q))) % oldRank P D q
  rw [IntegralMixedHeightTableQueryBits.oldCol, ite_eq_right hx, IntegralMixedOldHeightBits.oldRank_eq,
    (IntegralMixedFullHistoryFamilyBits.geometry P D).width q]
  rfl

end LeanCanny.Algebra.IntegralMixedHeightIndexBits
