/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationMomentProgram
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeFactor
/-! # A native normalization augmented entry uses its actual selected top entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits NativeControllerBranch
open IntegralMixedNormalizationMomentTasks
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] source access

private theorem routed_frame3 (P : Parameters) (F : Family) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool) (hp : isPhase .monomialFactor q) :
    IntegralMixedRoutineTaskBits.Frame P q
      (task P (source P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (source P F) q)) v)) := by
  have HP := IntegralCriticalFlatMomentEntryBits.request_parent P (source P F) q v
  have HF := task_frame P (source P F) route hr
    (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (source P F) q)) v)
    (by rw [HP]; change phase q = 3 at hp; omega)
  simpa only [HP] using HF

theorem frame3 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .monomialFactor q)
    (hc : (momentEntryProgram P a F h).controller.Requests answer budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff
    (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (source P F))
    (rowTask P (source P F)) (columnTask P (source P F)) (matrixTask P (source P F)) answer budget q c).mp hc
  rcases MatrixMoment.EntryBits.routed_cases
    (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h))
    (rowTask P (source P F)) (columnTask P (source P F)) (matrixTask P (source P F))
    (IntegralCriticalFlatMomentEntryBits.input P (source P F) q) hg with hr | hk | hm
  · rw [hchild, hr]
    exact routed_frame3 P F (rowQuery (source P F)) (row_parent _) q _ hp
  · rw [hchild, hk]
    exact routed_frame3 P F (columnQuery (source P F)) (column_parent _) q _ hp
  · rw [hchild, hm]
    exact routed_frame3 P F (matrixQuery (source P F)) (matrix_parent _) q _ hp

theorem moment_task_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : EntryMatches P F answer) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hq : IntegralMixedRoutineTaskBits.routine P q = 5) :
    answer (task P (source P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (source P F) q)) v)) =
      value P F (task P (source P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (source P F) q)) v)) := by
  let p := pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (source P F) q)) v
  have HP : original p = q := IntegralCriticalFlatMomentEntryBits.request_parent P (source P F) q v
  let z := route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p)
  have HZ : original z = q := (task_parent P route hr p).trans HP
  apply hx
  · unfold IntegralMixedVirtualCaps.valid task entryTask
    simp only [Function.comp_apply, IntegralCriticalFlatMatrixQuery.writer_birth,
      IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    change birth P (original z) < P.cap (RankedHistoryTask.root (original z))
    rw [HZ]
    exact hv
  · unfold task entryTask
    simp only [Function.comp_apply, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair]
    change IntegralMixedRoutineTaskBits.routine P (original z) = 5
    rw [HZ]
    exact hq
  · exact IntegralCriticalFlatMatrixQuery.writer_phase P .clearedHeight _

theorem replies3_of_entries (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : EntryMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    MomentEntryRepliesAt P a F h answer q := by
  have H := top_replies3 P a F h g q hv
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 h3
    exact (moment_task_reply P F answer hx (rowQuery (source P F)) (row_parent _) q _ hv hr).trans (H.1 h1 h2 h3)
  · intro h1 h2 h3 h4
    exact (moment_task_reply P F answer hx (columnQuery (source P F)) (column_parent _) q _ hv hr).trans (H.2.1 h1 h2 h3 h4)
  · intro h1 h2 h3 h4
    exact (moment_task_reply P F answer hx (matrixQuery (source P F)) (matrix_parent _) q _ hv hr).trans (H.2.2 h1 h2 h3 h4)

noncomputable def stage3 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (momentEntryProgram P a F h) ((momentEntryProgram P a F h).certificates (momentEntry_controls P a F h))
    (selected P .monomialFactor) (selected_FP P a .monomialFactor) (momentEntry P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)


theorem correct3 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hx : EntryMatches P F (fun q => residueBits (x q))) :
    Correct (stage3 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selected_iff P .monomialFactor q).mp hq
    exact value3 P a F h _ q (replies3_of_entries P a F h g _ hx q H.1 H.2.1)
  · intro q hq hr
    let C := momentEntryProgram P a F h
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) :=
      (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := frame3 P a F h _ (fun _ => 1) q (C.query q) ((selected_iff P .monomialFactor q).mp hq).2.2 HC
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) HF.1)
  · intro q c budget hq hc
    exact frame3 P a F h _ budget q c ((selected_iff P .monomialFactor q).mp hq).2.2 hc

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
