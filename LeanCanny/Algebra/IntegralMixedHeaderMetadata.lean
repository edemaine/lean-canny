/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeaderTables
/-! # Constructed full-history and raw-kind metadata from original header tables

All numeric readers below are derived from the two table writers and exact
syntactic representation. No polynomial degree algorithm is hidden here:
the cut degree is its explicit command field. The original frontend must
still provide total, bounded syntactic tables satisfying representation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeaderTablesBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryFamilyBits IntegralMixedCommandHeaderBits
open scoped Classical

theorem offset_unary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : Tables) (ht : Access T) (hr : Represents P D T) :
    UnaryFn (fun key => (IntegralMixedFullHistoryFamilyBits.selection P D key).rule.critical.offset.val) := by
  have HS := (selected_readers P a T ht).offset
  have HU := UnaryFn.fromBitsLE_min HS.bits_mem_FP (a.ambient.comp pairFst_mem_FP)
  refine HU.of_eq (fun key => ?_)
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HE := congrArg Header.offset (selected_eq P D T hr key)
  change (selected P T key).offset =
    (IntegralMixedFullHistoryFamilyBits.selection P D key).rule.critical.offset.val at HE
  rw [HE]
  exact min_eq_left (Nat.le_of_lt_succ (IntegralMixedFullHistoryFamilyBits.selection P D key).rule.critical.offset.isLt)

theorem fullMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : Tables) (ht : Access T) (hr : Represents P D T) : IntegralMixedFullHistoryFamilyBits.Metadata P D where
  offset := offset_unary P a D T ht hr
  objective := ((selected_readers P a T ht).objective).of_eq (fun key =>
    congrArg Header.objective (selected_eq P D T hr key))
  degree := ((selected_readers P a T ht).degree).of_eq (fun key =>
    congrArg Header.degree (selected_eq P D T hr key))
  context := ((producer_readers P a T ht).context).of_eq (fun key =>
    (congrArg Header.context (producer_eq P D T hr key)).trans (command_context _))
  coordinate := ((producer_readers P a T ht).coordinate).of_eq (fun key =>
    (congrArg Header.coordinate (producer_eq P D T hr key)).trans (command_coordinate _))

theorem selected_tag (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (IntegralMixedCommandHeaderBits.selection (IntegralMixedFullHistoryFamilyBits.selection P D key)).rawTag =
      IntegralMixedRawKindBits.tag (family P D) key := by
  change kindRawTag ((family P D).kind key) = IntegralMixedRawKindBits.tag (family P D) key
  cases hk : (family P D).kind key <;> simp only [IntegralMixedRawKindBits.tag, hk, kindRawTag]

theorem selected_coordinate (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (IntegralMixedCommandHeaderBits.selection (IntegralMixedFullHistoryFamilyBits.selection P D key)).coordinate =
      IntegralMixedRawKindBits.coordinate (family P D) key := by
  change kindCoordinate ((family P D).kind key) = IntegralMixedRawKindBits.coordinate (family P D) key
  cases hk : (family P D).kind key <;> simp only [IntegralMixedRawKindBits.coordinate, hk, kindCoordinate]

theorem selected_choice (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (IntegralMixedCommandHeaderBits.selection (IntegralMixedFullHistoryFamilyBits.selection P D key)).choice =
      IntegralMixedRawKindBits.choice (family P D) key := by
  change kindChoice ((family P D).kind key) = IntegralMixedRawKindBits.choice (family P D) key
  cases hk : (family P D).kind key <;> simp only [IntegralMixedRawKindBits.choice, hk, kindChoice]

theorem rawMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : Tables) (ht : Access T) (hr : Represents P D T) : IntegralMixedRawKindBits.Metadata (family P D) where
  tag := ((selected_readers P a T ht).rawTag).of_eq (fun key =>
    (congrArg Header.rawTag (selected_eq P D T hr key)).trans (selected_tag P D key))
  coordinate := ((selected_readers P a T ht).coordinate).of_eq (fun key =>
    (congrArg Header.coordinate (selected_eq P D T hr key)).trans (selected_coordinate P D key))
  choice := ((selected_readers P a T ht).choice).of_eq (fun key =>
    (congrArg Header.choice (selected_eq P D T hr key)).trans (selected_choice P D key))

end LeanCanny.Algebra.IntegralMixedHeaderTablesBits
