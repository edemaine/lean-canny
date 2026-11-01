/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionReplies
/-! # Native normalized companions charge both coefficient and producer-leading children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

def leadingChild (P : Parameters) : List Bool → List Bool :=
  IntegralMixedRoutineTaskBits.query P (birth P) .companion .originalCoefficient

theorem leadingChild_FP (P : Parameters) (a : Access P) : leadingChild P ∈ FP :=
  IntegralMixedRoutineTaskBits.query_FP P a (birth P)
    (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))) .companion .originalCoefficient

theorem leadingChild_frame (P : Parameters) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 6) (hp : isPhase .companion q) :
    IntegralMixedRoutineTaskBits.Frame P q (leadingChild P q) := by
  have HB : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
  refine ⟨IntegralMixedRoutineTaskBits.query_root P _ .companion .originalCoefficient q,
    IntegralMixedRoutineTaskBits.query_length P _ .companion .originalCoefficient q HB, ?_⟩
  apply IntegralMixedRoutineTaskBits.lower_phase P q _
    (IntegralMixedRoutineTaskBits.query_birth P _ .companion .originalCoefficient q HB)
  · rw [IntegralMixedRoutineTaskBits.query_routine, hr]
    rfl
  · rw [IntegralMixedRoutineTaskBits.query_phase]
    change phase q = 26 at hp
    change 0 < phase q
    omega

abbrev LeadingMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P .companion q = true → answer (leadingChild P q) = residueBits ((scalarFamily P F).leading q)

noncomputable def companionValue (P : Parameters) (F : Family) : List Bool → List Bool := (family P F).value

theorem companionValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = companionValue P F q := ⟨_, rfl⟩

noncomputable def companionStage (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : Machine :=
  ofTwoCalls (coefficientTask P F) (leadingChild P ∘ pairFst) (IntegralScalarGeneratorBits.chargedPost (scalarFamily P F))
    (coefficientTask_FP P a F h hd) (mem_FP_comp pairFst_mem_FP (leadingChild_FP P a))
    (IntegralScalarGeneratorBits.chargedPost_FP (scalarFamily P F) (scalarAccess P a F h hd))
    (selected P .companion) (selected_FP P a .companion) (companionValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

attribute [local irreducible] IntegralScalarGeneratorBits.chargedPost companionValue

theorem companion_result (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : NormalizationMatches P F answer) (hl : LeadingMatches P F answer)
    (q : List Bool) (hq : selected P .companion q = true) :
    DependentTwoCall.result (coefficientTask P F) (leadingChild P ∘ pairFst)
      (IntegralScalarGeneratorBits.chargedPost (scalarFamily P F)) answer q = companionValue P F q := by
  have HQ := (selected_iff P .companion q).mp hq
  unfold DependentTwoCall.result
  simp only [Function.comp_apply, pairFst_pair]
  rw [coefficient_reply P F g answer hm q HQ.1, hl q hq]
  have HE : (scalarFamily P F).toFamily.value q = companionValue P F q := by
    unfold scalarFamily IntegralScalarGeneratorBits.finFamily companionValue
    exact congrFun (PaddedIntegralGeneratorFinBits.value_eq (family P F)) q
  exact (IntegralScalarGeneratorBits.chargedPost_value (scalarFamily P F) q).trans HE

theorem companion_correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : NormalizationMatches P F (fun q => residueBits (x q)))
    (hl : LeadingMatches P F (fun q => residueBits (x q))) :
    Correct (companionStage P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · exact companion_result P F g _ hm hl
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
