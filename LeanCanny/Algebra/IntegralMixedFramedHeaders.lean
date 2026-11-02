/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
public import LeanCanny.Algebra.IntegralMixedHeaderTables

/-! # Native metadata from literal headers of changing-source instructions

The existing word readers apply after erasing each instruction's spatial
source from its header. Representation binds those words to actual framed
commands and fallbacks; it supplies no algebraic coefficient evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeaderBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryScript (Instruction)
open IntegralMixedFramedHistoryFamilyBits (Plan family instruction selection)
open IntegralMixedCommandHeaderBits (Header)
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical

def words {n B : ℕ} (cs : List (Instruction n B)) : List Bool :=
  WordList.encode (cs.reverse.map (fun c => IntegralMixedCommandHeaderBits.encode
    (IntegralMixedCommandHeaderBits.command c.command)))

theorem lookup_words {n B : ℕ} (cs : List (Instruction n B)) (fallback : Instruction n B)
    (hf : IntegralMixedCommandHeaderBits.command fallback.command = IntegralMixedCommandHeaderBits.zero)
    (i : ℕ) :
    IntegralMixedCommandHeaderBits.lookup (words cs) i = IntegralMixedCommandHeaderBits.command
      ((IntegralMixedFramedHistoryScript.chronological cs i).getD fallback).command := by
  unfold IntegralMixedCommandHeaderBits.lookup words IntegralMixedFramedHistoryScript.chronological
  rw [WordList.get_encode, List.getElem?_map]
  cases hi : cs.reverse[i]? with
  | none => exact IntegralMixedCommandHeaderBits.decode_nil.trans hf.symm
  | some c => exact IntegralMixedCommandHeaderBits.decode_encode _

structure Represents (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables) : Prop where
  commands : ∀ root, T.commands root = words (D.rules root)
  fallback : ∀ key,
    WordList.get (T.fallback (pairFst key)) (IntegralMixedHeaderTablesBits.fallbackIndex P key) =
      IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.selection (H.fallback key))

theorem producer_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (h : Represents P D H T) (key : List Bool) :
    IntegralMixedHeaderTablesBits.producer P T key =
      IntegralMixedCommandHeaderBits.command (instruction P D key).command := by
  unfold IntegralMixedHeaderTablesBits.producer
  rw [h.commands, lookup_words _ (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (by rfl)]
  rfl

theorem fallback_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (h : Represents P D H T) (key : List Bool) :
    IntegralMixedHeaderTablesBits.fallback P T key =
      IntegralMixedCommandHeaderBits.selection (H.fallback key) := by
  unfold IntegralMixedHeaderTablesBits.fallback IntegralMixedCommandHeaderBits.lookup
  rw [h.fallback, IntegralMixedCommandHeaderBits.decode_encode]

theorem selected_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (h : Represents P D H T) (key : List Bool) :
    IntegralMixedHeaderTablesBits.selected P T key =
      IntegralMixedCommandHeaderBits.selection (selection P D H key) := by
  unfold IntegralMixedHeaderTablesBits.selected
  rw [producer_eq P D H T h key, fallback_eq P D H T h key]
  unfold selection
  cases hc : (instruction P D key).command with
  | integer => simp [IntegralMixedCommandHeaderBits.command, IntegralMixedCommandHeaderBits.isCut,
      IntegralMixedCommandHeaderBits.zero]
  | critical => simp [IntegralMixedCommandHeaderBits.command, IntegralMixedCommandHeaderBits.isCut]
  | cut r k d ha hd => cases k <;> simp [IntegralMixedCommandHeaderBits.command,
      IntegralMixedCommandHeaderBits.selection, IntegralMixedCommandHeaderBits.kindContext,
      IntegralMixedCommandHeaderBits.isCut]

theorem rawMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : Represents P D H T) : IntegralMixedRawKindBits.Metadata (family P D H) := by
  have HS := IntegralMixedHeaderTablesBits.selected_readers P a T ht
  have HE := selected_eq P D H T hr
  constructor
  · apply HS.rawTag.of_eq
    intro key
    have HK := congrArg Header.rawTag (HE key)
    refine HK.trans ?_
    change IntegralMixedCommandHeaderBits.kindRawTag ((family P D H).kind key) = _
    cases hk : (family P D H).kind key <;>
      simp only [IntegralMixedCommandHeaderBits.kindRawTag, IntegralMixedRawKindBits.tag, hk]
  · apply HS.coordinate.of_eq
    intro key
    have HK := congrArg Header.coordinate (HE key)
    refine HK.trans ?_
    change IntegralMixedCommandHeaderBits.kindCoordinate ((family P D H).kind key) = _
    cases hk : (family P D H).kind key <;>
      simp only [IntegralMixedCommandHeaderBits.kindCoordinate, IntegralMixedRawKindBits.coordinate, hk]
  · apply HS.choice.of_eq
    intro key
    have HK := congrArg Header.choice (HE key)
    refine HK.trans ?_
    change IntegralMixedCommandHeaderBits.kindChoice ((family P D H).kind key) = _
    cases hk : (family P D H).kind key <;>
      simp only [IntegralMixedCommandHeaderBits.kindChoice, IntegralMixedRawKindBits.choice, hk]

theorem degree_binary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : Represents P D H T) : BinaryFn (family P D H).degree :=
  (IntegralMixedHeaderTablesBits.selected_readers P a T ht).degree.of_eq
    (fun key => congrArg Header.degree (selected_eq P D H T hr key))

theorem objective_binary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : Represents P D H T) : BinaryFn (fun key => ((family P D H).rule key).critical.objective) :=
  (IntegralMixedHeaderTablesBits.selected_readers P a T ht).objective.of_eq
    (fun key => congrArg Header.objective (selected_eq P D H T hr key))

theorem offset_unary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : Represents P D H T) : UnaryFn (fun key => ((family P D H).rule key).critical.offset.val) := by
  have HS := (IntegralMixedHeaderTablesBits.selected_readers P a T ht).offset
  have HU := UnaryFn.fromBitsLE_min HS.bits_mem_FP (a.ambient.comp pairFst_mem_FP)
  refine HU.of_eq (fun key => ?_)
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HE := congrArg Header.offset (selected_eq P D H T hr key)
  change (IntegralMixedHeaderTablesBits.selected P T key).offset =
    ((family P D H).rule key).critical.offset.val at HE
  rw [HE]
  exact min_eq_left (Nat.le_of_lt_succ ((family P D H).rule key).critical.offset.isLt)

noncomputable def routing (P : Parameters) (D : Plan P) : IntegralMixedOldBankCofactorBits.Routing where
  coordinate z := (instruction P D (IntegralMixedFullHistoryFamilyBits.producerKey z)).command.coordinate
  context z := (instruction P D (IntegralMixedFullHistoryFamilyBits.producerKey z)).command.context

theorem routingAccess (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : Represents P D H T) : IntegralMixedOldBankCofactorBits.RoutingAccess (routing P D) := by
  have HS := IntegralMixedHeaderTablesBits.producer_readers P a T ht
  have HC : BinaryFn (fun key => (instruction P D key).command.coordinate) :=
    HS.coordinate.of_eq (fun key => (congrArg Header.coordinate (producer_eq P D H T hr key)).trans
      (IntegralMixedCommandHeaderBits.command_coordinate _))
  have HX : BinaryFn (fun key => (instruction P D key).command.context) :=
    HS.context.of_eq (fun key => (congrArg Header.context (producer_eq P D H T hr key)).trans
      (IntegralMixedCommandHeaderBits.command_context _))
  exact ⟨HC.comp IntegralMixedFullHistoryFamilyBits.producerKey_FP,
    HX.comp IntegralMixedFullHistoryFamilyBits.producerKey_FP⟩

theorem routing_context_bound (P : Parameters) (D : Plan P) (z : List Bool) :
    (routing P D).context z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) :=
  (IntegralMixedFullHistoryScript.Command.context_le _).trans
    ((by decide : 4 ≤ 6).trans (IntegralMixedRoutineTaskBits.routine_cap P _))

theorem routing_coordinate_bound (P : Parameters) (D : Plan P) (z : List Bool) :
    (routing P D).coordinate z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := by
  have H := IntegralMixedFullHistoryScript.Command.coordinate_le
    (instruction P D (IntegralMixedFullHistoryFamilyBits.producerKey z)).command
  have HR : pairFst (IntegralMixedFullHistoryFamilyBits.producerKey z) =
      RankedHistoryTask.root (pairFst z) := pairFst_pair _ _
  have HB := H.trans_eq (congrArg P.ambient HR)
  exact (HB.trans (Nat.le_succ _)).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

end LeanCanny.Algebra.IntegralMixedFramedHeaderBits
