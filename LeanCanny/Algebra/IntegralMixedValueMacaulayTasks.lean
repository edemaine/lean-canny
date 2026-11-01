/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalBranch
public import LeanCanny.Algebra.MacaulayIntegralQueryBounds
public import LeanCanny.Algebra.IntegralMixedValueMacaulayEntry

/-! # Native shifted-system coefficient tasks for the actual value Macaulay matrix

The rectangular row is held in slot 8 and its column in slot 9. The child
keeps both integral basis indices and requests phase 23 at the decoded
system row and difference monomial. The monomial uses the original spatial
grid and therefore fits the one original scalar cap.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical

noncomputable abbrev layout (P : Parameters) (F : Family) :=
  IntegralMixedValueMacaulayEntry.layout (IntegralMixedVirtualTaskBits.family P F)

def packet (P : Parameters) (q : List Bool) : List Bool :=
  MacaulayFullBoxBits.entryPacket q (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q)

theorem packet_FP (P : Parameters) (a : Access P) : packet P ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (get_binary P a .slot8).bits_mem_FP
    (mem_FP_pair (get_binary P a .slot9).bits_mem_FP
      (mem_FP_pair (get_binary P a .row).bits_mem_FP (get_binary P a .col).bits_mem_FP)))

theorem layout_controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (layout P F).Controls :=
  IntegralMixedValueMacaulayEntry.layout_controls _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)

noncomputable def queryPacket (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  MacaulayIntegralEntryRequest.query (layout P F) (packet P q)
theorem queryPacket_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : queryPacket P F ∈ FP :=
  mem_FP_comp (packet_FP P a) (MacaulayIntegralEntryRequest.query_FP _ (layout_controls P a F h))

noncomputable def sourceRow (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  IntegralReciprocalEntryRequest.row (queryPacket P F q)
noncomputable def difference (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  IntegralReciprocalEntryRequest.target (queryPacket P F q)
theorem sourceRow_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (sourceRow P F) :=
  IntegralReciprocalEntryRequest.row_binary.comp (queryPacket_FP P a F h)
theorem difference_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (difference P F) :=
  IntegralReciprocalEntryRequest.target_binary.comp (queryPacket_FP P a F h)

theorem sourceRow_eq (P : Parameters) (F : Family) (q : List Bool) :
    sourceRow P F q = get P .slot8 q / count ((layout P F).arity q) ((layout P F).width q) := by
  rw [sourceRow, queryPacket, packet, MacaulayIntegralQueryBounds.query_packet]
  simp only [IntegralReciprocalEntryRequest.row, MacaulayFullBoxBits.idx_entryPacket, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem difference_eq (P : Parameters) (F : Family) (q : List Bool) :
    difference P F q = MacaulayIntegralQueryBounds.differenceRank (layout P F) q
      (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q) := by
  rw [difference, queryPacket, packet, MacaulayIntegralQueryBounds.query_packet]
  simp only [IntegralReciprocalEntryRequest.target, MacaulayFullBoxBits.shift_entryPacket, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem queryPacket_eq (P : Parameters) (F : Family) (q : List Bool) :
    queryPacket P F q = MacaulayFullBoxBits.entryPacket q (sourceRow P F q) (difference P F q) (get P .row q) (get P .col q) := by
  rw [sourceRow_eq, difference_eq, queryPacket, packet, MacaulayIntegralQueryBounds.query_packet]

theorem sourceRow_lt (P : Parameters) (F : Family) (q : List Bool)
    (h : MacaulayIntegralEntryRequest.request (layout P F) (packet P q)) :
    sourceRow P F q < (layout P F).arity q := by
  rw [sourceRow_eq]
  exact MacaulayIntegralQueryBounds.sourceRow_lt _ _ _ _ _ _ h

theorem sourceRow_cap (P : Parameters) (F : Family) (q : List Bool) :
    sourceRow P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  rw [sourceRow_eq]
  exact (Nat.div_le_self _ _).trans (get_le P .slot8 q)

theorem difference_lt (P : Parameters) (F : Family) (q : List Bool) :
    difference P F q < count ((layout P F).arity q) ((layout P F).width q) := by
  rw [difference_eq]
  exact MacaulayIntegralQueryBounds.differenceRank_lt _ _ _ _ _ _

theorem difference_cap (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) :
    difference P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  ((difference_lt P F q).trans (IntegralMixedValueTaskBounds.columns_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q)).le.trans
    (IntegralMixedValueTaskBounds.scalar_le_root_cap P F g q)

noncomputable def sourceTask (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .pscEntry .relativeFactor .slot8 (sourceRow P F)
noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (sourceTask P F) .pscEntry .relativeFactor .target (difference P F)

theorem sourceTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : sourceTask P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (sourceRow_binary P a F h)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (sourceTask_FP P a F h) _ _ _ _ (difference_binary P a F h)

theorem sourceTask_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (sourceTask P F q) = RankedHistoryTask.root q :=
  IntegralMixedValueFieldQuery.query_root P id _ _ _ _ q
theorem query_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P (sourceTask P F) _ _ _ _ q).trans (sourceTask_root P F q)
theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q :=
  (IntegralMixedValueFieldQuery.query_birth P (sourceTask P F) _ _ _ _ q).trans
    (IntegralMixedValueFieldQuery.query_birth P id _ _ _ _ q)

theorem query_get (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 2 else if f = .target then difference P F q else
      if f = .slot8 then sourceRow P F q else get P f q := by
  rw [query, IntegralMixedValueFieldQuery.query_get, sourceTask_root]
  rw [sourceTask, IntegralMixedValueFieldQuery.query_get]
  simp only [id_eq, min_eq_left (sourceRow_cap P F q), min_eq_left (difference_cap P F g q)]
  cases f <;> rfl

theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P (sourceTask P F) .pscEntry .relativeFactor .target (difference P F) q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved P id .pscEntry .relativeFactor .slot8 (sourceRow P F) q (by decide))

theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P (sourceTask P F) .pscEntry .relativeFactor .target (difference P F) q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_modulus P id .pscEntry .relativeFactor .slot8 (sourceRow P F) q (by decide))

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 24) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  refine ⟨query_root P F q, ?_, ?_⟩
  · have HL := IntegralMixedValueFieldQuery.query_length P (sourceTask P F) .pscEntry .relativeFactor .target (difference P F) q
    have HW : wordBudget P (sourceTask P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [sourceTask_root]
    exact HL.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_phase P q _ (query_birth P F q)
    · rw [query, IntegralMixedValueFieldQuery.query_routine, hr]
      rfl
    · rw [query, IntegralMixedValueFieldQuery.query_phase, hp]
      decide

end LeanCanny.Algebra.IntegralMixedValueMacaulayTasks
