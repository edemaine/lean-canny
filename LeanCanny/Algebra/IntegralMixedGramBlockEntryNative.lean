/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramBlockEntryTasks
public import LeanCanny.Algebra.IntegralNaturalBlockEntry

/-! # Actual Gram integer-block entries use the verified negative Gram sum -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramBlockEntryNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedGramBlockEntryTasks
open IntegralMixedGramCharacteristicSource
open scoped Classical
attribute [local irreducible] residueBits

theorem block_entry (P : Parameters) (F : Family) (q : List Bool) (a b : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralCriticalTotalSnapshotBits.blockMatrix (source P F) q) a b =
        table P F q (a / (source P F).rank q) (b / (source P F).rank q)
          (a % (source P F).rank q) (b % (source P F).rank q) := by
  let := (source P F).ring q
  exact IntegralNaturalBlockEntry.entry_all ((source P F).basis q) ((source P F).matrix q)
    ((source P F).rank_pos q) a b

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralCriticalTotalSnapshotBits.blockMatrix (source P F) q) (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem child_value (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueGramSumSource.value P F (query P F q) = value P F q := by
  unfold IntegralMixedValueGramSumSource.value value
  rw [← IntegralMixedGramCharacteristicSnapshot.table_current,
    IntegralMixedGramCharacteristicSnapshot.table_snapshot, query_saved]
  simp only [query_get, reduceCtorEq, ite_false, ite_true]
  rw [← IntegralMixedGramCharacteristicSnapshot.table_snapshot, block_entry]
  exact congrArg (fun m : ℕ => residueBits
    (table P F q (spatialRow P F q) (spatialCol P F q) (basisRow P F q) (basisCol P F q) : ZMod m))
      (query_modulus P F q)

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request _ := true
  query := query P F
  immediate _ := []
  finish := pairSnd
theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (program P F).Controls :=
  ⟨constFn_mem_FP [true], query_FP P a F h, constFn_mem_FP [], pairSnd_mem_FP⟩

abbrev RepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  answer (query P F q) = IntegralMixedValueGramSumSource.value P F (query P F q)
theorem value_at (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F answer q) :
    (program P F).value answer q = value P F q := by
  simp only [SingleCall.Program.value, program, ite_true, pairSnd_pair]
  exact he.trans (child_value P F q)

def Selected (P : Parameters) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 3 ∧ isPhase .actionEntry q
noncomputable instance (P : Parameters) (q : List Bool) : Decidable (Selected P q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected_FP (P : Parameters) (a : Access P) : FPPred (Selected P) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 3)).and (isPhase_FP .actionEntry))

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := (program P F).controller
  certificates := (program P F).certificates (controls P a F h)
  selected q := decide (Selected P q)
  selected_FP := (selected_FP P a).flag_mem_FP
  model := value P F
  clock _ := 1
  clock_binary := BinaryFn.const 1
  stateBound := IntegralMixedValueHomogeneousRequest.stateBound P
  stateBound_unary := IntegralMixedValueHomogeneousRequest.stateBound_unary P a

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (he : ∀ q, Selected P q → RepliesAt P F answer q) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (program P F).halted_after answer q
  · intro q t hq hh
    exact ((program P F).output_when_halted answer q t hh).trans (value_at P F answer q (he q (of_decide_eq_true hq)))
  · intro q t hq
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    apply (program P F).state_length_of_bound answer q t ((modulus P q).size)
    intro _
    change (answer (query P F q)).length ≤ _
    rw [he q (of_decide_eq_true hq), child_value]
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    have HS : Selected P q := of_decide_eq_true hq
    have HQ := (SingleCall.Program.requests_iff (program P F) answer budget q c).mp hc
    rw [HQ.2]
    exact query_frame P F q HS.2.1

end LeanCanny.Algebra.IntegralMixedGramBlockEntryNative
