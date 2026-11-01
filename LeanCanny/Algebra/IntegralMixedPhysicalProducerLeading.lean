/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarMatches
public import LeanCanny.Algebra.IntegralClearedCriticalLeadingCoefficient
/-! # Actual physical producer-leading scalars use one charged common-leading child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalProducerLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selected (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧
    isPhase .originalCoefficient q ∧ get P .slot15 q = 1)

theorem selected_FP (P : Parameters) (a : Access P) : (fun q => [selected P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 6)).and
      ((isPhase_FP .originalCoefficient).and ((get_binary P a .slot15).eq (BinaryFn.const 1))))).flag_mem_FP

theorem selected_iff (P : Parameters) (q : List Bool) : selected P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧
      isPhase .originalCoefficient q ∧ get P .slot15 q = 1 := by simp only [selected, decide_eq_true_eq]

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request _ := true
  query := IntegralMixedScalarQueryBits.commonLeading P
  immediate _ := []
  finish := IntegralClearedCriticalLeadingBits.powerPost (critical P F)

theorem controls (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :
    (program P F).Controls :=
  ⟨constFn_mem_FP [true], IntegralMixedScalarQueryBits.scalarQuery_FP P a .monomialFactor,
    constFn_mem_FP [], IntegralClearedCriticalLeadingBits.powerPost_FP (critical P F) (criticalAccess P a F h)⟩

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  reply (IntegralMixedScalarQueryBits.commonLeading P q) =
    IntegralCriticalLeadingBits.value (critical P F).toEuler.toGradient.toFrozen q

noncomputable def value (P : Parameters) (F : Family) := IntegralClearedCriticalLeadingBits.value (critical P F)

attribute [local irreducible] IntegralClearedCriticalLeadingBits.powerPost

theorem value_at (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : RepliesAt P F reply q) : (program P F).value reply q = value P F q := by
  change IntegralClearedCriticalLeadingBits.powerPost (critical P F)
    (pair q (reply (IntegralMixedScalarQueryBits.commonLeading P q))) = _
  rw [he]
  unfold IntegralCriticalLeadingBits.value
  rw [IntegralClearedCriticalLeadingBits.powerPost_packet]
  unfold value IntegralClearedCriticalLeadingBits.value IntegralClearedCriticalLeadingBits.integer
    IntegralClearedCriticalBounds.commonLeading
  simp only [Int.cast_pow]

noncomputable def machine (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (program P F) ((program P F).certificates (controls P a F h))
    (selected P) (selected_FP P a) (value P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (he : ∀ q, selected P q = true → RepliesAt P F (fun q => residueBits (x q)) q) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    exact value_at P F _ q (he q hq)
  · intro q hq _
    have HQ := (selected_iff P q).mp hq
    have HF := IntegralMixedScalarQueryBits.scalar_frame P .monomialFactor q (by rw [HQ.2.1]; decide)
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (IntegralMixedScalarQueryBits.commonLeading P q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) HF.1)
  · intro q c budget hq hc
    have HQ := (selected_iff P q).mp hq
    obtain ⟨_, rfl⟩ := ((program P F).requests_iff _ budget q c).mp hc
    exact IntegralMixedScalarQueryBits.scalar_frame P .monomialFactor q (by rw [HQ.2.1]; decide)

theorem canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F q := ⟨_, rfl⟩

theorem replies_of_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : IntegralMixedPhysicalScalarReplyBits.Matches P F answer) (q : List Bool) (hq : selected P q = true) :
    RepliesAt P F answer q := by
  have HQ := (selected_iff P q).mp hq
  change answer (IntegralMixedScalarQueryBits.commonLeading P q) = commonLeading P F q
  exact (IntegralMixedPhysicalScalarReplyBits.query_match P F answer hm .monomialFactor q
    (by unfold IntegralMixedPhysicalScalarReplyBits.allowed; decide) HQ.1 HQ.2.2.2).trans (commonLeading_child P F q)

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : IntegralMixedPhysicalScalarReplyBits.Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h x (replies_of_matches P F _ hm)

end LeanCanny.Algebra.IntegralMixedPhysicalProducerLeadingBits
