/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatMomentTasks
public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactor
public import LeanCanny.Algebra.MatrixMomentEntryControllerLocal
public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
/-! # Flat augmented-moment entries request actual action entries

The three nonzero block cases share a fresh phase19 writer. Local replies
are confined to the actually selected row, column, or interior packet.
Zero entries have no child. Each child retains the original root once.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatMomentEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatMomentTasks
set_option backward.isDefEq.respectTransparency false
abbrev Source := IntegralBerkowitzBlockBits.Source

noncomputable def matrixSize (P : Parameters) (S : Source) (c : List Bool) : ℕ :=
  ((IntegralCriticalFlatMomentBits.source P S).dimension c + 2) * (IntegralCriticalFlatMomentBits.source P S).rank c

noncomputable def matrixPacket (P : Parameters) (S : Source) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (get P .row c % matrixSize P S c))
    (BinaryNatCode.encode (get P .col c % matrixSize P S c)))

theorem matrixPacket_FP (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : matrixPacket P S ∈ FP := by
  have HN : BinaryFn (matrixSize P S) :=
    ((IntegralCriticalFlatMomentBits.access P a S h).dimension.add (BinaryFn.const 2)).mul
      (IntegralCriticalFlatMomentBits.access P a S h).rank
  exact mem_FP_pair id_mem_FP (mem_FP_pair ((get_binary P a .row).mod HN).bits_mem_FP
    ((get_binary P a .col).mod HN).bits_mem_FP)

noncomputable def input (P : Parameters) (S : Source) : List Bool → List Bool :=
  IntegralBlockMomentBits.outerPacket (IntegralCriticalFlatMomentBits.source P S) ∘ matrixPacket P S

theorem input_FP (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : input P S ∈ FP :=
  mem_FP_comp (matrixPacket_FP P a S h)
    (IntegralBlockMomentBits.outerPacket_FP _ (IntegralCriticalFlatMomentBits.access P a S h))

theorem input_parent (P : Parameters) (S : Source) (c : List Bool) :
    IntegralBerkowitzBlockBits.original (input P S c) = c := by
  simp only [input, Function.comp_apply, IntegralBlockMomentBits.outerPacket,
    matrixPacket, IntegralBerkowitzBlockBits.original,
    IntegralBlockMomentBits.context, pairFst_pair]

theorem request_parent (P : Parameters) (S : Source) (c v : List Bool) :
    IntegralBerkowitzBlockBits.original (pair (pairFst (input P S c)) v) = c := by
  simpa only [IntegralBerkowitzBlockBits.original, pairFst_pair] using input_parent P S c

noncomputable def bits (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : MatrixMoment.EntryBits.Access :=
  IntegralBlockMomentBits.bitsAccess (IntegralCriticalFlatMomentBits.source P S) (IntegralCriticalFlatMomentBits.access P a S h)

noncomputable def program (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : SingleCall.Program :=
  MatrixMoment.EntryBits.program (bits P a S h) (input P S) (rowTask P S) (columnTask P S) (matrixTask P S)

theorem controls (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : (program P a S h).Controls := by
  have HB : BinaryFn (fun q => (IntegralCriticalFlatMomentBits.source P S).dimension (pairFst q)) :=
    (IntegralCriticalFlatMomentBits.access P a S h).dimension.comp pairFst_mem_FP
  have HD : (bits P a S h).dimension ∈ FP := HB.bits_mem_FP
  exact MatrixMoment.EntryBits.program_controls (bits P a S h) HD (input P S) _ _ _ (input_FP P a S h)
    (rowTask_FP P a S h) (columnTask_FP P a S h) (matrixTask_FP P a S h)

abbrev RepliesAt (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  MatrixMoment.EntryBits.RepliesAt (bits P a S h) (input P S) (rowTask P S) (columnTask P S) (matrixTask P S) answer c

theorem value (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P a S h answer c) :
    (program P a S h).value answer c =
      IntegralBlockMomentBits.entryProgram (IntegralCriticalFlatMomentBits.source P S) (IntegralCriticalFlatMomentBits.access P a S h)
        (matrixPacket P S c) :=
  MatrixMoment.EntryBits.program_value_local (bits P a S h) (input P S) _ _ _ answer c he

theorem value_entry (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P a S h answer c)
    (i j : Fin (((IntegralCriticalFlatMomentBits.source P S).dimension c + 2) * (IntegralCriticalFlatMomentBits.source P S).rank c))
    (hi : get P .row c = i.val) (hj : get P .col c = j.val) :
    (program P a S h).value answer c =
      residueBits (((IntegralCriticalFlatMomentBits.source P S).powerMatrix c i j : ℤ) :
        ZMod ((IntegralCriticalFlatMomentBits.source P S).modulus c)) := by
  rw [value P a S h answer c he]
  simp only [matrixPacket, matrixSize, hi, hj, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
  exact IntegralBlockMomentBits.entry_correct (IntegralCriticalFlatMomentBits.source P S)
    (IntegralCriticalFlatMomentBits.access P a S h) c i j

private theorem routed_frame (P : Parameters) (S : Source) (route : List Bool → List Bool)
    (hr : ∀ p, IntegralBerkowitzBlockBits.original (route p) = IntegralBerkowitzBlockBits.original (IntegralBerkowitzBlockBits.original p))
    (c v : List Bool) (hp : isPhase .momentEntry c) :
    RankedHistoryTask.root (task P S route (pair (pairFst (input P S c)) v)) = RankedHistoryTask.root c ∧
      (task P S route (pair (pairFst (input P S c)) v)).length ≤ wordBudget P c ∧
        rank P (task P S route (pair (pairFst (input P S c)) v)) < rank P c := by
  have HQ := request_parent P S c v
  have HP : 19 < phase (IntegralBerkowitzBlockBits.original (pair (pairFst (input P S c)) v)) := by
    rw [HQ]
    change phase c = 21 at hp
    omega
  have H := task_frame P S route hr (pair (pairFst (input P S c)) v) HP
  rw [HQ] at H
  exact H

theorem requests_frame (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) (hp : isPhase .momentEntry c)
    (hc : (program P a S h).controller.Requests answer budget c child) :
    RankedHistoryTask.root child = RankedHistoryTask.root c ∧ child.length ≤ wordBudget P c ∧ rank P child < rank P c := by
  obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff (bits P a S h) (input P S)
    (rowTask P S) (columnTask P S) (matrixTask P S) answer budget c child).mp hc
  rcases MatrixMoment.EntryBits.routed_cases (bits P a S h) (rowTask P S) (columnTask P S) (matrixTask P S) (input P S c) hg with hr | hc | hm
  · rw [hchild, hr]
    exact routed_frame P S (IntegralBerkowitzBlockBits.rowQuery S) (row_parent S) c _ hp
  · rw [hchild, hc]
    exact routed_frame P S (IntegralBerkowitzBlockBits.columnQuery S) (column_parent S) c _ hp
  · rw [hchild, hm]
    exact routed_frame P S (IntegralBerkowitzBlockBits.matrixQuery S) (matrix_parent S) c _ hp

def stateBound (P : Parameters) (c : List Bool) : ℕ :=
  2 * c.length + 4 + IntegralCriticalHistoryEvaluator.residueWidth P c

theorem stateBound_unary (P : Parameters) (a : Access P) : UnaryFn (stateBound P) :=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem state_length (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus P q)) (c : List Bool)
    (hp : isPhase .momentEntry c) (t : ℕ) :
    (SingleCall.encState (((program P a S h).controller.reference (fun q => residueBits (x q)))^[t]
      ((program P a S h).controller.initial c))).length ≤ stateBound P c := by
  apply (program P a S h).state_length_of_bound
  intro hr
  have HC : (program P a S h).controller.Requests (fun q => residueBits (x q)) (fun _ => 1) c ((program P a S h).query c) :=
    ((program P a S h).requests_iff _ _ c _).mpr ⟨hr, rfl⟩
  have HE := (requests_frame P a S h (fun q => residueBits (x q)) (fun _ => 1) c _ hp HC).1
  have HV := IntegralCriticalHistoryEvaluator.answer_length P x ((program P a S h).query c)
  have HW : IntegralCriticalHistoryEvaluator.residueWidth P ((program P a S h).query c) =
      IntegralCriticalHistoryEvaluator.residueWidth P c := congrArg (fun r => (numericCap P r).size) HE
  exact HV.trans_eq HW

end LeanCanny.Algebra.IntegralCriticalFlatMomentEntryBits
