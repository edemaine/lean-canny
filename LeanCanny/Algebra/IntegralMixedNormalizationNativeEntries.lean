/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationRawQuery
public import LeanCanny.Algebra.IntegralMixedNormalizationCharacteristic
public import LeanCanny.Algebra.IntegralMixedNormalizationMomentQuery
public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
/-! # Native normalization matrix leaves with strictly lower raw-cut requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

def rawProgram (P : Parameters) (F : Family) : SingleCall.Program where
  request _ := true
  query := rawQuery P F
  immediate _ := []
  finish := pairSnd

theorem raw_controls (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : (rawProgram P F).Controls :=
  ⟨constFn_mem_FP [true], rawQuery_FP P a F hd, constFn_mem_FP [], pairSnd_mem_FP⟩

abbrev RawMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 4 → isPhase .companion q →
    answer q = rawCutValue P F q

noncomputable def stage0 (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : Machine :=
  ofSingleCall (rawProgram P F) ((rawProgram P F).certificates (raw_controls P a F hd))
    (selected P .originalCoefficient) (selected_FP P a .originalCoefficient) (value P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct0 (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hx : RawMatches P F (fun q => residueBits (x q))) :
    Correct (stage0 P a F hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selected_iff P .originalCoefficient q).mp hq
    have HV : IntegralMixedVirtualCaps.valid P (rawQuery P F q) := by
      unfold IntegralMixedVirtualCaps.valid
      rw [rawQuery_birth, rawQuery_root]
      exact H.1
    have HE := (hx _ HV (rawQuery_routine P F q) (rawQuery_phase P F q)).trans (rawQuery_value P F g q)
    simpa only [SingleCall.Program.value, rawProgram, ite_true, pairSnd_pair] using HE
  · intro q _ _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (rawQuery P F q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (rawQuery_root P F q))
  · intro q c budget hq hc
    have HE := ((rawProgram P F).requests_iff _ budget q c).mp hc
    rw [HE.2]
    exact rawQuery_frame P F q ((selected_iff P .originalCoefficient q).mp hq).2.1

theorem value_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    value P F (IntegralCriticalFlatEulerBits.next P p q) = value P F q := by
  unfold value
  rw [saved_next, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_modulus]

theorem next_frame (P : Parameters) (p : Phase) (q : List Bool) (hp : p.code < phase q) :
    IntegralMixedRoutineTaskBits.Frame P q (IntegralCriticalFlatEulerBits.next P p q) := by
  refine ⟨IntegralCriticalFlatEulerBits.next_root P p q, ?_, ?_⟩
  · exact child_length P id (birth P) p _ q (min_le_right _ _)
  · apply IntegralMixedRoutineTaskBits.lower_phase P q _ (IntegralCriticalFlatEulerBits.next_birth P p q)
    · unfold IntegralMixedRoutineTaskBits.routine
      rw [IntegralCriticalFlatEulerBits.next_get]
    · rw [IntegralCriticalFlatEulerBits.next_phase]
      exact hp

def entryProgram (P : Parameters) : SingleCall.Program where
  request _ := true
  query := IntegralCriticalFlatEulerBits.next P .originalCoefficient
  immediate _ := []
  finish := pairSnd

theorem entry_controls (P : Parameters) (a : Access P) : (entryProgram P).Controls :=
  ⟨constFn_mem_FP [true], IntegralCriticalFlatEulerBits.next_FP P a .originalCoefficient, constFn_mem_FP [], pairSnd_mem_FP⟩

abbrev TopMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 → isPhase .originalCoefficient q →
    answer q = value P F q

noncomputable def stage2 (P : Parameters) (a : Access P) (F : Family) : Machine :=
  ofSingleCall (entryProgram P) ((entryProgram P).certificates (entry_controls P a))
    (selected P .clearedHeight) (selected_FP P a .clearedHeight) (value P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct2 (P : Parameters) (a : Access P) (F : Family)
    (x : (q : List Bool) → ZMod (modulus P q)) (hx : TopMatches P F (fun q => residueBits (x q))) :
    Correct (stage2 P a F) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selected_iff P .clearedHeight q).mp hq
    have HV : IntegralMixedVirtualCaps.valid P (IntegralCriticalFlatEulerBits.next P .originalCoefficient q) := by
      unfold IntegralMixedVirtualCaps.valid
      rw [IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatEulerBits.next_root]
      exact H.1
    have HR : IntegralMixedRoutineTaskBits.routine P (IntegralCriticalFlatEulerBits.next P .originalCoefficient q) = 5 := by
      unfold IntegralMixedRoutineTaskBits.routine
      rw [IntegralCriticalFlatEulerBits.next_get]
      simpa only [IntegralMixedRoutineTaskBits.routine] using H.2.1
    have HE := (hx _ HV HR (IntegralCriticalFlatEulerBits.next_phase P .originalCoefficient q)).trans (value_next P F .originalCoefficient q)
    simpa only [SingleCall.Program.value, entryProgram, ite_true, pairSnd_pair] using HE
  · intro q _ _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (IntegralCriticalFlatEulerBits.next P .originalCoefficient q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (IntegralCriticalFlatEulerBits.next_root P .originalCoefficient q))
  · intro q c budget hq hc
    have HE := ((entryProgram P).requests_iff _ budget q c).mp hc
    rw [HE.2]
    apply next_frame P .originalCoefficient q
    have HP := ((selected_iff P .clearedHeight q).mp hq).2.2
    change phase q = 2 at HP
    change 0 < phase q
    omega

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
