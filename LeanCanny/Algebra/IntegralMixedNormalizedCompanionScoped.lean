/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionCurrent
public import LeanCanny.Algebra.IntegralMixedVirtualContextLeaves
/-! # Creating-cut companions need normalization replies only in their actual contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev ScopedNormalizationMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .eulerSum q → IntegralMixedVirtualContextBits.context P q → answer q = normalizedValue P F q

theorem leadingTask_context (P : Parameters) (F : Family) (q : List Bool) :
    get P .slot15 (leadingTask P F q) = get P .slot15 q := by
  simp only [leadingTask, Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_get,
    reduceCtorEq, ite_false, leadingPacket, pairFst_pair]

theorem coefficientTask_context (P : Parameters) (F : Family) (q : List Bool) :
    get P .slot15 (coefficientTask P F q) = get P .slot15 q := by
  simp only [coefficientTask, Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_get,
    reduceCtorEq, ite_false, IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair]

theorem leading_reply_scoped (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : ScopedNormalizationMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hx : IntegralMixedVirtualContextBits.context P q) :
    answer (leadingTask P F q) = IntegralMixedNormalizationTopBits.leadingValue P F q := by
  have HP : pairFst (leadingPacket P F q) = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P (leadingTask P F q) := by
    unfold IntegralMixedVirtualCaps.valid leadingTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_birth,
      IntegralMixedCoefficientQueryBits.writer_root, HP]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P (leadingTask P F q) = 5 :=
    IntegralMixedCoefficientQueryBits.writer_routine P .normalization .eulerSum _
  have HC : isPhase .eulerSum (leadingTask P F q) :=
    IntegralMixedCoefficientQueryBits.writer_phase P .normalization .eulerSum _
  exact (hm _ HV HR HC (by unfold IntegralMixedVirtualContextBits.context at hx ⊢; rw [leadingTask_context]; exact hx)).trans (leadingTask_value P F g q)

theorem coefficient_reply_scoped (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : ScopedNormalizationMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hx : IntegralMixedVirtualContextBits.context P q) :
    answer (coefficientTask P F q) = residueBits
      ((scalarFamily P F).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P F) q)
        ((scalarFamily P F).oldRow q) ((scalarFamily P F).oldCol q)) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P (coefficientTask P F q) := by
    unfold IntegralMixedVirtualCaps.valid coefficientTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_birth,
      IntegralMixedCoefficientQueryBits.writer_root, HP]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P (coefficientTask P F q) = 5 :=
    IntegralMixedCoefficientQueryBits.writer_routine P .normalization .eulerSum _
  have HC : isPhase .eulerSum (coefficientTask P F q) :=
    IntegralMixedCoefficientQueryBits.writer_phase P .normalization .eulerSum _
  exact (hm _ HV HR HC (by unfold IntegralMixedVirtualContextBits.context at hx ⊢; rw [coefficientTask_context]; exact hx)).trans (coefficientTask_value P F g q hv)

theorem leading_correct_scoped (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : ScopedNormalizationMatches P F (fun q => residueBits (x q))) :
    Correct (leadingStage P a F hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have HQ := (selected_iff P .originalCoefficient q).mp hq
    change pairSnd (pair q (residueBits (x (leadingTask P F q)))) = _
    rw [pairSnd_pair]
    exact leading_reply_scoped P F g _ hm q HQ.1 HQ.2.2.2
  · intro q hq _
    have HQ := (selected_iff P .originalCoefficient q).mp hq
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (leadingTask P F q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (leading_frame P F q HQ.2.1).1)
  · intro q c budget hq hc
    have HQ := (selected_iff P .originalCoefficient q).mp hq
    obtain ⟨_, rfl⟩ := ((leadingProgram P F).requests_iff _ budget q c).mp hc
    exact leading_frame P F q HQ.2.1

theorem companion_result_scoped (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : ScopedNormalizationMatches P F answer) (hl : LeadingMatches P F answer)
    (q : List Bool) (hq : selected P .companion q = true) :
    DependentTwoCall.result (coefficientTask P F) (leadingChild P ∘ pairFst)
      (IntegralScalarGeneratorBits.chargedPost (scalarFamily P F)) answer q = companionValue P F q := by
  have HQ := (selected_iff P .companion q).mp hq
  unfold DependentTwoCall.result
  simp only [Function.comp_apply, pairFst_pair]
  rw [coefficient_reply_scoped P F g answer hm q HQ.1 HQ.2.2.2, hl q hq]
  have HE : (scalarFamily P F).toFamily.value q = companionValue P F q := by
    unfold scalarFamily IntegralScalarGeneratorBits.finFamily companionValue
    exact congrFun (PaddedIntegralGeneratorFinBits.value_eq (family P F)) q
  exact (IntegralScalarGeneratorBits.chargedPost_value (scalarFamily P F) q).trans HE

theorem companion_correct_scoped (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : ScopedNormalizationMatches P F (fun q => residueBits (x q)))
    (hl : LeadingMatches P F (fun q => residueBits (x q))) :
    Correct (companionStage P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · exact companion_result_scoped P F g _ hm hl
  · intro q hq
    have HQ := (selected_iff P .companion q).mp hq
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (coefficientTask P F q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (coefficientTask_frame P F q HQ.2.1).1)
  · intro q _
    obtain ⟨z, hz⟩ := companionValue_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
  · intro q c budget hq hc
    have HQ := (selected_iff P .companion q).mp hq
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q c hc with hleft | hright
    · rw [hleft]
      exact coefficientTask_frame P F q HQ.2.1
    · rw [hright]
      simpa only [Function.comp_apply, pairFst_pair] using leadingChild_frame P q HQ.2.1 HQ.2.2.1

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
