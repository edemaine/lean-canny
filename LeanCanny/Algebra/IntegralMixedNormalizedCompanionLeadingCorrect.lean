/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionLeading
/-! # Native normalized producer-leading correctness uses the current coefficient reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem leading_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 6) :
    IntegralMixedRoutineTaskBits.Frame P q (leadingTask P F q) := by
  have HP : pairFst (leadingPacket P F q) = q := pairFst_pair _ _
  have HF := IntegralMixedCoefficientQueryBits.writer_frame P .normalization .eulerSum (leadingPacket P F q)
    (by rw [HP, hr]; decide)
  simpa only [HP, leadingTask, Function.comp_apply] using HF

theorem leading_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : NormalizationMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) :
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
  exact (hm _ HV HR HC).trans (leadingTask_value P F g q)

theorem leading_correct (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : NormalizationMatches P F (fun q => residueBits (x q))) :
    Correct (leadingStage P a F hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have HQ := (selected_iff P .originalCoefficient q).mp hq
    change pairSnd (pair q (residueBits (x (leadingTask P F q)))) = _
    rw [pairSnd_pair]
    exact leading_reply P F g _ hm q HQ.1
  · intro q hq _
    have HQ := (selected_iff P .originalCoefficient q).mp hq
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (leadingTask P F q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (leading_frame P F q HQ.2.1).1)
  · intro q c budget hq hc
    have HQ := (selected_iff P .originalCoefficient q).mp hq
    obtain ⟨_, rfl⟩ := ((leadingProgram P F).requests_iff _ budget q c).mp hc
    exact leading_frame P F q HQ.2.1

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
