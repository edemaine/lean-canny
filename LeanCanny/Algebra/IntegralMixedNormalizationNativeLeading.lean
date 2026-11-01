/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationLeadingQueries
public import LeanCanny.Computation.NativeTwoCallBranch
/-! # The leading branch requests its exact index and then its scalar residue -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def leadingStage (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofTwoCalls (indexTask P F) (leadingTask P) leadingPost (indexTask_FP P a F h) (leadingTask_FP P a) leadingPost_FP
    (selected P .eulerSum) (selected_FP P a .eulerSum) (leadingValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem leading_correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hi : IndexMatches P F (fun q => residueBits (x q))) (hc : CharacteristicMatches P F (fun q => residueBits (x q))) :
    Correct (leadingStage P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · intro q hq
    have H := (selected_iff P .eulerSum q).mp hq
    exact leading_result P F g _ hi hc q H.1 H.2.1
  · intro q _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (indexTask P F q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (IntegralMixedNormalizationFieldBits.query_root P id .clearedGridSum _ _ q))
  · intro q _
    obtain ⟨z, hz⟩ := leadingValue_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
  · intro q c budget hq hreq
    have H := (selected_iff P .eulerSum q).mp hq
    have HP := H.2.2
    change phase q = 14 at HP
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q c hreq with hl | hr
    · rw [hl]
      unfold indexTask
      exact IntegralMixedNormalizationFieldBits.query_frame P id .clearedGridSum _ _ q
        (by simp only [id_eq]; change 8 < phase q; omega)
    · rw [hr]
      unfold leadingTask
      have HF := IntegralMixedNormalizationFieldBits.query_frame P pairFst .productPower
        (fun z => modulus P (pairFst z)) (fun z => Nat.fromBitsLE (pairSnd z))
        (pair q (residueBits (x (indexTask P F q))))
        (by simp only [pairFst_pair]; change 6 < phase q; omega)
      simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
