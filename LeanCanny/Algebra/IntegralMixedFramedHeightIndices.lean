/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightTableMatrix
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
/-! # Actual normalized old-basis rows in physical and nilpotent height queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightIndexBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedOldHeightBits (bankFamily oldRank)
set_option backward.isDefEq.respectTransparency false

theorem row_physical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (hx : get P .slot15 q = 1) :
    IntegralMixedFramedHeightTableMatrixBits.row P D J q = IntegralMixedHeightNaturalEntries.index
      ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .row q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldRow P q = get P .row q % oldRank P D J q
  rw [IntegralMixedHeightTableQueryBits.oldRow, ite_eq_left hx, IntegralMixedFramedOldHeightBits.oldRank_eq]

theorem col_physical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (hx : get P .slot15 q = 1) :
    IntegralMixedFramedHeightTableMatrixBits.col P D J q = IntegralMixedHeightNaturalEntries.index
      ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .col q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldCol P q = get P .col q % oldRank P D J q
  rw [IntegralMixedHeightTableQueryBits.oldCol, ite_eq_left hx, IntegralMixedFramedOldHeightBits.oldRank_eq]

theorem row_virtual (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (hx : get P .slot15 q ≠ 1) :
    IntegralMixedFramedHeightTableMatrixBits.row P D J q = IntegralMixedHeightNaturalEntries.oldIndex
      ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .row q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldRow P q =
    (get P .row q / 2 ^ ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q))) % oldRank P D J q
  rw [IntegralMixedHeightTableQueryBits.oldRow, ite_eq_right hx, IntegralMixedFramedOldHeightBits.oldRank_eq,
    (IntegralMixedFramedHistoryFamilyBits.geometry P D J).width q]
  rfl

theorem col_virtual (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (hx : get P .slot15 q ≠ 1) :
    IntegralMixedFramedHeightTableMatrixBits.col P D J q = IntegralMixedHeightNaturalEntries.oldIndex
      ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .col q) := by
  apply Fin.ext
  change IntegralMixedHeightTableQueryBits.oldCol P q =
    (get P .col q / 2 ^ ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q))) % oldRank P D J q
  rw [IntegralMixedHeightTableQueryBits.oldCol, ite_eq_right hx, IntegralMixedFramedOldHeightBits.oldRank_eq,
    (IntegralMixedFramedHistoryFamilyBits.geometry P D J).width q]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedHeightIndexBits
