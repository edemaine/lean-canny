/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQuery
/-! # Exact creating-command and basis-index readback

The creating query retains the source packet's actual prefix. Wrapped matrix
indices are represented exactly whenever that prefix is a valid native birth.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction prefixLength)
open IntegralMixedFramedProducerActualBits (instruction_context_snapshot instruction_coordinate_snapshot framed_saved_prefix)
open scoped Classical

theorem query_valid (P : Parameters) (D : Plan P) (q : List Bool)
    (hb : sourceBirth P q<P.cap (root q)) : IntegralMixedVirtualCaps.valid P (query P D q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_birth,query_root]
  exact hb

theorem sourceRank_le (P : Parameters) (q : List Bool) (hb : sourceBirth P q<P.cap (root q)) :
    sourceRank P q≤numericCap P (root q) :=
  born_rank_le P _ (by unfold birthCap; omega)

theorem query_row (P : Parameters) (D : Plan P) (q : List Bool)
    (hb : sourceBirth P q<P.cap (root q)) : get P .row (query P D q)=rowIndex P q := by
  rw [query_get]
  exact min_eq_left ((Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)).le.trans (sourceRank_le P q hb))

theorem query_col (P : Parameters) (D : Plan P) (q : List Bool)
    (hb : sourceBirth P q<P.cap (root q)) : get P .col (query P D q)=colIndex P q := by
  rw [query_get]
  exact min_eq_left ((Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)).le.trans (sourceRank_le P q hb))

theorem query_saved_root (P : Parameters) (D : Plan P) (q : List Bool) :
    pairFst (IntegralMixedVirtualTaskBits.saved P (query P D q))=
      pairFst (PaddedIntegralGeneratorSource.base q) := by
  rw [IntegralMixedFullHistoryFamilyBits.saved_root,query_root]
  rfl

theorem query_saved_birth (P : Parameters) (D : Plan P) (q : List Bool) :
    prefixLength P (IntegralMixedVirtualTaskBits.saved P (query P D q))=
      prefixLength P (PaddedIntegralGeneratorSource.base q) := by
  rw [framed_saved_prefix,query_birth]
  rfl

theorem query_actual_context (P : Parameters) (D : Plan P) (q : List Bool) :
    get P .slot15 (query P D q)=
      (instruction P D (IntegralMixedVirtualTaskBits.saved P (query P D q))).command.context := by
  rw [query_context]
  change (instruction P D (PaddedIntegralGeneratorSource.base q)).command.context=_
  rw [instruction_context_snapshot,instruction_context_snapshot,query_saved_root,query_saved_birth]

theorem query_actual_coordinate (P : Parameters) (D : Plan P) (q : List Bool) :
    get P .slot13 (query P D q)=
      (instruction P D (IntegralMixedVirtualTaskBits.saved P (query P D q))).command.coordinate := by
  rw [query_coordinate]
  change (instruction P D (PaddedIntegralGeneratorSource.base q)).command.coordinate=_
  rw [instruction_coordinate_snapshot,instruction_coordinate_snapshot,query_saved_root,query_saved_birth]

theorem query_context_le (P : Parameters) (D : Plan P) (q : List Bool) :
    get P .slot15 (query P D q)≤4 := by
  rw [query_actual_context]
  exact IntegralMixedFullHistoryScript.Command.context_le _

end LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
