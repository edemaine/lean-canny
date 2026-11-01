/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramMomentMatches
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Native augmented Gram entries from the actual action component -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralCriticalFlatMomentTasks
open scoped Classical

theorem frame21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .momentEntry q)
    (hc : (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).controller.Requests answer budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  apply IntegralMixedMatrixFrames.frame_of_ordinary
  · obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff
      (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
      (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F))
      (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F)) answer budget q c).mp hc
    rcases MatrixMoment.EntryBits.routed_cases
      (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
      (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F))
      (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q) hg with hr | hk | hm
    · rw [hchild, hr]
      exact moment_routed_routine P (characteristic P F) (IntegralBerkowitzBlockBits.rowQuery (characteristic P F)) (row_parent _) q _
    · rw [hchild, hk]
      exact moment_routed_routine P (characteristic P F) (IntegralBerkowitzBlockBits.columnQuery (characteristic P F)) (column_parent _) q _
    · rw [hchild, hm]
      exact moment_routed_routine P (characteristic P F) (IntegralBerkowitzBlockBits.matrixQuery (characteristic P F)) (matrix_parent _) q _
  · exact IntegralCriticalFlatMomentEntryBits.requests_frame P a (characteristic P F) (characteristicAccess P a F h) answer budget q c hp hc


def Selected21 (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 3 ∧ isPhase .momentEntry q ∧
    get P .row q < IntegralMixedGramMomentMatrix.size P F q ∧ get P .col q < IntegralMixedGramMomentMatrix.size P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected21 P F q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem moment_size_binary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : BinaryFn (IntegralMixedGramMomentMatrix.size P F) :=
  ((momentAccess P a F h).dimension.add (BinaryFn.const 2)).mul (momentAccess P a F h).rank

theorem selected21_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    FPPred (Selected21 P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 3)).and
      ((isPhase_FP .momentEntry).and (((get_binary P a .row).lt (moment_size_binary P a F h)).and
        ((get_binary P a .col).lt (moment_size_binary P a F h)))))

noncomputable def stage21 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).controller
  certificates := (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).certificates
    (IntegralCriticalFlatMomentEntryBits.controls P a (characteristic P F) (characteristicAccess P a F h))
  selected q := decide (Selected21 P F q)
  selected_FP := (selected21_FP P a F h).flag_mem_FP
  model := entryValue P F
  clock _ := 1
  clock_binary := BinaryFn.const 1
  stateBound := IntegralCriticalFlatMomentEntryBits.stateBound P
  stateBound_unary := IntegralCriticalFlatMomentEntryBits.stateBound_unary P a

theorem correct21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (ha : ActionMatches P F (fun q => residueBits (x q))) :
    Correct (stage21 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).halted_after _ q
  · intro q t hq hh
    have HS : Selected21 P F q := of_decide_eq_true hq
    have HE := value21 P a F h _ q (moment_replies_of_action P a F h g _ ha q HS.1 HS.2.1)
    have HV : (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).value
        (fun q => residueBits (x q)) q = entryValue P F q := by
      simpa only [entryValue, momentEntry, Nat.mod_eq_of_lt HS.2.2.2.1, Nat.mod_eq_of_lt HS.2.2.2.2] using HE
    exact ((IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
      (characteristicAccess P a F h)).output_when_halted _ q t hh).trans HV
  · intro q t hq
    have HS : Selected21 P F q := of_decide_eq_true hq
    exact IntegralCriticalFlatMomentEntryBits.state_length P a (characteristic P F) (characteristicAccess P a F h) x q HS.2.2.1 t
  · intro q c budget hq hc
    have HS : Selected21 P F q := of_decide_eq_true hq
    exact frame21 P a F h _ budget q c HS.2.2.1 hc

end LeanCanny.Algebra.IntegralMixedGramUpperBits
