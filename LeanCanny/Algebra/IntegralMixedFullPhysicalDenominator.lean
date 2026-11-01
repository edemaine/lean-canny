/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeDenominator
public import LeanCanny.Algebra.IntegralMixedFullPhysicalFamily
public import LeanCanny.Algebra.IntegralMixedOldBankProvenance
/-! # Literal full mixed-history provenance for physical scalar denominators -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalOldBankBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false
theorem writer_packet_saved (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (i : ℕ) (hi : i < count P F q)
    (hc : R.context (packet P F q i) ≤ numericCap P (RankedHistoryTask.root q)) :
    IntegralMixedPhysicalTaskBits.saved P (writer P R (packet P F q i)) =
      pair (RankedHistoryTask.root q) (pair (BinaryNatCode.encode (count P F q - 1 - i)) (BinaryNatCode.encode (R.context (packet P F q i)))) := by
  have HR : RankedHistoryTask.root (writer P R (packet P F q i)) = RankedHistoryTask.root q := by
    rw [writer_root]
    exact pairFst_pair _ _ |> congrArg RankedHistoryTask.root
  have HC : get P .slot15 (writer P R (packet P F q i)) = R.context (packet P F q i) := by
    apply IntegralMixedRoutineContextQuery.query_context
    simpa only [packet, pairFst_pair] using hc
  simp only [IntegralMixedPhysicalTaskBits.saved, HR, writer_packet_birth P F g R q i hi, HC]

theorem writer_packet_coordinate (P : Parameters) (F : Family) (R : Routing) (q : List Bool) (i : ℕ)
    (hc : R.coordinate (packet P F q i) ≤ numericCap P (RankedHistoryTask.root q)) :
    get P .slot13 (writer P R (packet P F q i)) = R.coordinate (packet P F q i) := by
  apply IntegralMixedRoutineContextQuery.query_coordinate
  simpa only [packet, pairFst_pair] using hc
end LeanCanny.Algebra.IntegralMixedPhysicalOldBankBits
namespace LeanCanny.Algebra.IntegralMixedFullPhysicalDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedFullPhysicalBits
set_option backward.isDefEq.respectTransparency false

noncomputable def creatingCommand (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (key : List Bool) := (creating P D key).getD defaultCommand

structure ProducerMetadata (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) : Prop where
  context : BinaryFn (fun key => (creatingCommand P D key).context)
  coordinate : BinaryFn (fun key => (creatingCommand P D key).coordinate)

def producerKey (z : List Bool) : List Bool := pair (RankedHistoryTask.root (pairFst z))
  (pair (BinaryNatCode.encode (IntegralMixedPhysicalOldBankBits.producerBirth z)) [])

theorem producerKey_FP : producerKey ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP)
    (mem_FP_pair IntegralMixedPhysicalOldBankBits.producerBirth_binary.bits_mem_FP (constFn_mem_FP []))

noncomputable def routing (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) : IntegralMixedPhysicalOldBankBits.Routing where
  coordinate z := (creatingCommand P D (producerKey z)).coordinate
  context z := (creatingCommand P D (producerKey z)).context

theorem routingAccess (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (h : ProducerMetadata P D) :
    IntegralMixedPhysicalOldBankBits.RoutingAccess (routing P D) where
  coordinate := h.coordinate.comp producerKey_FP
  context := h.context.comp producerKey_FP

theorem routing_context_bound (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (z : List Bool) :
    (routing P D).context z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) :=
  (Command.context_le _).trans ((by decide : 4 ≤ 6).trans (IntegralMixedRoutineTaskBits.routine_cap P _))

theorem routing_coordinate_bound (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (z : List Bool) :
    (routing P D).coordinate z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := by
  have H := Command.coordinate_le (creatingCommand P D (producerKey z))
  have HR : pairFst (producerKey z) = RankedHistoryTask.root (pairFst z) := pairFst_pair _ _
  have HB := H.trans_eq (congrArg P.ambient HR)
  exact (HB.trans (Nat.le_succ _)).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

theorem origin_command (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    chosen (commands P D key) i =
      (chronological (D.rules (pairFst key)) (prefixLength P key - 1 - i.val)).getD defaultCommand := by
  have HI : i.val < prefixLength P key := lt_of_lt_of_eq i.isLt (family_birth P D key)
  have HB : prefixLength P key - 1 - i.val < prefixLength P key := by omega
  have HA := padded_producer_command (D.rules (pairFst key)) (prefixLength P key) i
  have HC := paddedPast_chronological (D.rules (pairFst key)) (prefixLength P key) _ HB
  exact Option.some.inj (HA.symm.trans HC)

noncomputable def producerLeading (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (key : List Bool) (i : Fin ((family P D).birth key)) : ℤ :=
  leading (birthState (initial P D (pairFst key)) (commands P D key)
    (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
    (older_bound (commands P D key) (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
    (chosen (commands P D key) i)

theorem retained_leading (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    ((family P D).state key).bank.denominator i = producerLeading P D key i := origin_denominator P D key i

abbrev ProducerRepliesAt (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i : Fin (IntegralMixedPhysicalOldBankBits.count P (family P D) q),
    reply (IntegralMixedPhysicalOldBankBits.writer P (routing P D)
      (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i.val)) =
      residueBits (producerLeading P D (IntegralMixedPhysicalTaskBits.saved P q) i : ZMod (modulus P q))

theorem replies (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (reply : List Bool → List Bool) (q : List Bool)
    (he : ProducerRepliesAt P D reply q) : IntegralMixedPhysicalOldBankBits.RepliesAt P (family P D) (routing P D) reply q := by
  intro i
  exact (he i).trans (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (retained_leading P D (IntegralMixedPhysicalTaskBits.saved P q) i).symm)

theorem producer_frame (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (q : List Bool) (i : ℕ)
    (hi : i < IntegralMixedPhysicalOldBankBits.count P (family P D) q) :
    IntegralMixedRoutineTaskBits.Frame P q (IntegralMixedPhysicalOldBankBits.writer P (routing P D)
      (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i)) :=
  IntegralMixedPhysicalOldBankBits.writer_packet_frame P (family P D) (geometry P D) (routing P D) q i hi

theorem producer_key (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (q : List Bool) (i : ℕ)
    (hi : i < IntegralMixedPhysicalOldBankBits.count P (family P D) q) :
    IntegralMixedPhysicalTaskBits.saved P
      (IntegralMixedPhysicalOldBankBits.writer P (routing P D) (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i)) =
      pair (RankedHistoryTask.root q)
        (pair (BinaryNatCode.encode (IntegralMixedPhysicalOldBankBits.count P (family P D) q - 1 - i))
          (BinaryNatCode.encode ((routing P D).context (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i)))) := by
  apply IntegralMixedPhysicalOldBankBits.writer_packet_saved P (family P D) (geometry P D) (routing P D) q i hi
  simpa only [IntegralMixedPhysicalOldBankBits.packet, pairFst_pair] using
    routing_context_bound P D (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i)

theorem producer_coordinate (P : Parameters) (D : IntegralMixedFullPhysicalBits.Data P) (q : List Bool) (i : ℕ) :
    get P .slot13 (IntegralMixedPhysicalOldBankBits.writer P (routing P D)
      (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i)) =
      (routing P D).coordinate (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i) := by
  apply IntegralMixedPhysicalOldBankBits.writer_packet_coordinate
  simpa only [IntegralMixedPhysicalOldBankBits.packet, pairFst_pair] using
    routing_coordinate_bound P D (IntegralMixedPhysicalOldBankBits.packet P (family P D) q i)

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullPhysicalBits.Data P) (h : IntegralMixedFullPhysicalBits.Metadata P D)
    (hr : ProducerMetadata P D) (hp : IntegralMixedPhysicalNativeDenominatorBits.Primitive P (family P D)) :=
  IntegralMixedPhysicalNativeDenominatorBits.machine P a (family P D) (inputMetadata P a D h) (geometry P D)
    (routing P D) (routingAccess P D hr) hp

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullPhysicalBits.Data P) (h : IntegralMixedFullPhysicalBits.Metadata P D)
    (hr : ProducerMetadata P D) (hp : IntegralMixedPhysicalNativeDenominatorBits.Primitive P (family P D))
    (reply : List Bool → List Bool)
    (he : ∀ q, IntegralMixedPhysicalNativeDenominatorBits.selected P q = true → ProducerRepliesAt P D reply q) :
    NativeControllerBranch.Correct (machine P a D h hr hp) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalNativeDenominatorBits.correct P a (family P D) (inputMetadata P a D h) (geometry P D)
    (routing P D) (routingAccess P D hr) hp reply (fun q hq => replies P D reply q (he q hq))
end LeanCanny.Algebra.IntegralMixedFullPhysicalDenominatorBits
