/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationFactorValue
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeEntries
/-! # Normalization factors request only current top entries and moments -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def factorSize (P : Parameters) (F : Family) (q : List Bool) : ℕ := powerDimension (source P F) q

theorem factorSize_binary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : BinaryFn (factorSize P F) :=
  (((access P a F h).dimension.add (BinaryFn.const 1)).mul
    ((access P a F h).dimension.add (BinaryFn.const 1))).mul (access P a F h).rank

noncomputable def selected5 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P .productEntry q && decide (get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q)

theorem selected5_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected5 P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a .productEntry)).and
    (((get_binary P a .row).lt (factorSize_binary P a F h)).and
      ((get_binary P a .col).lt (factorSize_binary P a F h)))).flag_mem_FP
    (fun q => by
      cases hb : selected P .productEntry q <;>
        by_cases hf : get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q <;>
          simp [selected5, hb, hf])

theorem selected5_iff (P : Parameters) (F : Family) (q : List Bool) : selected5 P F q = true ↔
    (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .productEntry q) ∧
      get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q := by
  simp only [selected5, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

theorem diagonal_parent (P : Parameters) (F : Family) (q : List Bool) :
    original (diagonalQuery (source P F) (outer P F q)) = q :=
  (IntegralCriticalFlatRelativeFactorBits.diagonal_original _ _).trans (outer_parent P F q)

attribute [local irreducible] source access selector value factorValue momentValue

theorem factor_query (P : Parameters) (F : Family) (q : List Bool) :
    (factorProgram P F).query q = if selector (source P F) (outer P F q) = [false, true] then
      diagonalChild P F q else momentChild P F q := by
  simp only [factorProgram, SingleCall.Program.requery, entryController,
    IntegralBerkowitzBlockBits.program, Function.comp_apply, IntegralBerkowitzBlockBits.child]
  rfl

theorem factor_frame (P : Parameters) (F : Family) (q : List Bool) (hp : isPhase .productEntry q) :
    IntegralMixedRoutineTaskBits.Frame P q ((factorProgram P F).query q) := by
  have HP : phase q = 5 := hp
  rw [factor_query]
  split_ifs
  · have HF := entryTask_frame P .clearedHeight (diagonalQuery (source P F) (outer P F q))
      (by rw [diagonal_parent]; change 2 < phase q; omega)
    simpa only [diagonal_parent, diagonalChild] using HF
  · have HF := momentTask_frame P (outer P F q) (by rw [outer_parent]; omega)
    simpa only [outer_parent, momentChild] using HF

abbrev EntryMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .clearedHeight q → answer q = value P F q

abbrev MomentPowerMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .factorPower q → answer q = momentValue P F q

theorem diagonal_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : EntryMatches P F answer) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    answer (diagonalChild P F q) = value P F (diagonalChild P F q) := by
  apply hx
  · unfold IntegralMixedVirtualCaps.valid diagonalChild entryTask
    simp only [IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root,
      pairFst_pair, diagonal_parent]
    exact hv
  · unfold diagonalChild entryTask
    simpa only [IntegralMixedMatrixFrames.matrix_routine, pairFst_pair, diagonal_parent] using hr
  · exact IntegralCriticalFlatMatrixQuery.writer_phase P .clearedHeight _

theorem moment_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : MomentPowerMatches P F answer) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    answer (momentChild P F q) = momentValue P F (momentChild P F q) := by
  apply hx
  · unfold IntegralMixedVirtualCaps.valid momentChild
    rw [momentTask_birth, momentTask_root, outer_parent]
    exact hv
  · unfold momentChild
    rw [momentTask_routine, outer_parent]
    exact hr
  · exact momentTask_phase P _

noncomputable def stage5 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (factorProgram P F) ((factorProgram P F).certificates (factor_controls P a F h))
    (selected5 P F) (selected5_FP P a F h) (factorValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct5 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (he : EntryMatches P F (fun q => residueBits (x q)))
    (hm : MomentPowerMatches P F (fun q => residueBits (x q))) :
    Correct (stage5 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selected5_iff P F q).mp hq
    exact factor_value_at P a F h g _ q H.1.1
      (fun _ => diagonal_reply P F _ he q H.1.1 H.1.2.1)
      (fun _ => moment_reply P F _ hm q H.1.1 H.1.2.1) ⟨_, H.2.1⟩ ⟨_, H.2.2⟩ rfl rfl
  · intro q hq _
    have HF := factor_frame P F q ((selected5_iff P F q).mp hq).1.2.2
    exact (IntegralCriticalHistoryEvaluator.answer_length P x ((factorProgram P F).query q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) HF.1)
  · intro q c budget hq hc
    obtain ⟨_, rfl⟩ := ((factorProgram P F).requests_iff _ budget q c).mp hc
    exact factor_frame P F q ((selected5_iff P F q).mp hq).1.2.2

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
