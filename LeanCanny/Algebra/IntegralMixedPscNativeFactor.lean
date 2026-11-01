/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscRelativeModel
public import LeanCanny.Algebra.IntegralMixedPscMomentMatches
/-! # Native PSC characteristic factors request only actual phase-zero entries and phase-two moments -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits NativeControllerBranch
open scoped Classical

noncomputable def factorSize (P : Parameters) (F : Family) (q : List Bool) : ℕ := powerDimension (characteristic P F) q

theorem factorSize_binary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : BinaryFn (factorSize P F) :=
  (((characteristicAccess P a F h).dimension.add (BinaryFn.const 1)).mul
    ((characteristicAccess P a F h).dimension.add (BinaryFn.const 1))).mul (characteristicAccess P a F h).rank

noncomputable def selected3 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P F .monomialFactor q && decide (get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q)

theorem selected3_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected3 P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a F h .monomialFactor)).and
    (((get_binary P a .row).lt (factorSize_binary P a F h)).and
      ((get_binary P a .col).lt (factorSize_binary P a F h)))).flag_mem_FP
    (fun q => by
      cases hb : selected P F .monomialFactor q <;>
        by_cases hf : get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q <;>
          simp [selected3, hb, hf])

theorem selected3_iff (P : Parameters) (F : Family) (q : List Bool) : selected3 P F q = true ↔
    (Domain P F q ∧ isPhase .monomialFactor q) ∧
      get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q := by
  simp only [selected3, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

theorem diagonal_parent (P : Parameters) (F : Family) (q : List Bool) :
    original (diagonalQuery (characteristic P F) (outer P F q)) = q :=
  (IntegralCriticalFlatRelativeFactorBits.diagonal_original _ _).trans (outer_parent P F q)

attribute [local irreducible] IntegralMixedPscCharacteristicBits.source characteristicAccess selector IntegralMixedPscMatrixModel.actionValue factorValue momentValue

theorem factor_query (P : Parameters) (F : Family) (q : List Bool) :
    (factorProgram P F).query q = if selector (characteristic P F) (outer P F q) = [false, true] then
      diagonalChild P F q else momentChild P F q := by
  simp only [factorProgram, SingleCall.Program.requery, entryController,
    IntegralBerkowitzBlockBits.program, Function.comp_apply, IntegralBerkowitzBlockBits.child]
  rfl

theorem factor_frame (P : Parameters) (F : Family) (q : List Bool) (hp : isPhase .monomialFactor q) :
    IntegralMixedRoutineTaskBits.Frame P q ((factorProgram P F).query q) := by
  have HP : phase q = 3 := hp
  rw [factor_query]
  split_ifs
  · have HF := IntegralMixedPscMomentTasks.entryWriter_frame P (characteristic P F) (diagonalQuery (characteristic P F) (outer P F q))
      (by rw [diagonal_parent]; omega)
    simpa only [diagonal_parent, diagonalChild] using HF
  · have HF := momentTask_frame P (outer P F q) (by rw [outer_parent]; omega)
    simpa only [outer_parent, momentChild] using HF

abbrev MomentPowerMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P F .clearedHeight q = true → answer q = momentValue P F q

theorem momentTask_domain (P : Parameters) (F : Family) (z : List Bool) (hq : Domain P F (original z)) :
    Domain P F (momentTask P z) := by
  apply domain_transport P F (original z) _ hq
  · exact momentTask_root P z
  · exact momentTask_birth P z
  · exact (momentTask_routine P z).trans hq.2.1
  · simp only [momentTask, IntegralCriticalFlatEulerBits.next_get,
      IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]
  · simp only [momentTask, IntegralCriticalFlatEulerBits.next_get,
      IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]

theorem diagonal_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : ActionMatches P F answer) (q : List Bool) (hq : Domain P F q) :
    answer (diagonalChild P F q) = IntegralMixedPscMatrixModel.actionValue P F (diagonalChild P F q) := by
  apply hx
  apply decide_eq_true
  refine ⟨?_, IntegralCriticalFlatMatrixQuery.writer_phase P .originalCoefficient _⟩
  exact entryWriter_domain P F (characteristic P F) _ ((diagonal_parent P F q).symm ▸ hq)

theorem moment_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : MomentPowerMatches P F answer) (q : List Bool) (hq : Domain P F q) :
    answer (momentChild P F q) = momentValue P F (momentChild P F q) := by
  apply hx
  apply decide_eq_true
  exact ⟨momentTask_domain P F _ ((outer_parent P F q).symm ▸ hq), momentTask_phase P _⟩

noncomputable def stage3 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (factorProgram P F) ((factorProgram P F).certificates (factor_controls P a F h))
    (selected3 P F) (selected3_FP P a F h) (factorValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct3 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (he : ActionMatches P F (fun q => residueBits (x q)))
    (hm : MomentPowerMatches P F (fun q => residueBits (x q))) :
    Correct (stage3 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selected3_iff P F q).mp hq
    exact factor_value_at P a F h g _ q H.1.1.1
      (fun _ => diagonal_reply P F _ he q H.1.1)
      (fun _ => moment_reply P F _ hm q H.1.1) ⟨_, H.2.1⟩ ⟨_, H.2.2⟩ rfl rfl
  · intro q hq _
    have HF := factor_frame P F q ((selected3_iff P F q).mp hq).1.2
    exact (IntegralCriticalHistoryEvaluator.answer_length P x ((factorProgram P F).query q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) HF.1)
  · intro q c budget hq hc
    obtain ⟨_, rfl⟩ := ((factorProgram P F).requests_iff _ budget q c).mp hc
    exact factor_frame P F q ((selected3_iff P F q).mp hq).1.2

end LeanCanny.Algebra.IntegralMixedPscUpperBits
