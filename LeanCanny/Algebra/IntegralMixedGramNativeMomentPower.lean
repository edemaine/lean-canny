/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramNativeMomentEntry
/-! # Native virtual moment powering from current augmented entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 3 ∧ isPhase p q)

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 3)).and (isPhase_FP p))).flag_mem_FP

theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 3 ∧ isPhase p q := by
  simp only [selected, decide_eq_true_eq]

noncomputable def momentValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  (IntegralBerkowitzBlockBits.momentFamily (characteristic P F)).value (IntegralCriticalFlatMomentBits.packet P q)

noncomputable def stage22 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralCriticalFlatMomentBits.controller P a (characteristic P F) (characteristicAccess P a F h)
  certificates := IntegralCriticalFlatMomentBits.certificates P a (characteristic P F) (characteristicAccess P a F h)
  selected := selected P .momentPower
  selected_FP := selected_FP P a .momentPower
  model := momentValue P F
  clock := IntegralCriticalFlatMomentBits.clock P (characteristic P F)
  clock_binary := IntegralCriticalFlatMomentBits.clock_binary P a (characteristic P F) (characteristicAccess P a F h)
  stateBound := IntegralCriticalFlatMomentBits.stateBound P (characteristic P F)
  stateBound_unary := IntegralCriticalFlatMomentBits.stateBound_unary P a (characteristic P F) (characteristicAccess P a F h)

attribute [local irreducible] IntegralMixedGramCharacteristicSource.source characteristicAccess

theorem correct22 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool)
    (he : ∀ q, selected P .momentPower q = true → IntegralCriticalFlatMomentBits.RepliesAt P (characteristic P F) answer q) :
    Correct (stage22 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatMomentBits.halted_after P a (characteristic P F) (characteristicAccess P a F h) answer q (he q hq)
  · intro q t hq hh
    exact IntegralCriticalFlatMomentBits.output_when_halted P a (characteristic P F) (characteristicAccess P a F h) answer q (he q hq) t hh
  · intro q t hq
    change (((IntegralCriticalFlatMomentBits.controller P a (characteristic P F) (characteristicAccess P a F h)).reference answer)^[t]
      ((IntegralCriticalFlatMomentBits.controller P a (characteristic P F) (characteristicAccess P a F h)).initial q)).length ≤ _
    exact IntegralCriticalFlatMomentBits.state_length P a (characteristic P F)
      (characteristicAccess P a F h) answer q (he q hq) t
  · intro q c budget hq hc
    obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
      (IntegralBlockMomentBits.powerAccess (IntegralCriticalFlatMomentBits.source P (characteristic P F))
        (IntegralCriticalFlatMomentBits.access P a (characteristic P F) (characteristicAccess P a F h)))
      (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer q (he q hq) budget c hc
    have HP := ((selected_iff P .momentPower q).mp hq).2.2
    have HS : Phase.momentEntry.code < phase (pairFst
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) := by
      simp only [pairFst_pair]
      change 21 < phase q
      change phase q = 22 at HP
      omega
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .momentEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) HS

abbrev MomentMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 → isPhase .momentEntry q →
    answer q = entryValue P F q

theorem moment_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : MomentMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 3) :
    IntegralCriticalFlatMomentBits.RepliesAt P (characteristic P F) answer q := by
  intro i j
  let c := IntegralCriticalFlatMatrixQuery.writer P .momentEntry
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HC : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 3 := by
    simpa only [c, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair] using hr
  exact (hx c HC HR (IntegralCriticalFlatMatrixQuery.writer_phase P .momentEntry _)).trans
    (moment_entry_child P F g q hv i j)

theorem correct22_of_matches (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (hx : MomentMatches P F answer) :
    Correct (stage22 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply correct22 P a F h answer
  intro q hq
  have HS := (selected_iff P .momentPower q).mp hq
  exact moment_replies P F g answer hx q HS.1 HS.2.1

end LeanCanny.Algebra.IntegralMixedGramUpperBits
