/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerChildren
/-! # Native integer companions use their two current original-data leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev CoefficientMatches (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P .criticalCoefficient q = true → answer q = coefficientValue P D q

theorem coefficient_reply (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (hm : CoefficientMatches P D answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hx : get P .slot15 q = 0) :
    answer (coefficientTask P D q) = residueBits
      ((scalarFamily P D).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P D) q)
        ((scalarFamily P D).oldRow q) ((scalarFamily P D).oldCol q)) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P D) q) = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P (coefficientTask P D q) := by
    unfold IntegralMixedVirtualCaps.valid coefficientTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_birth, IntegralMixedCoefficientQueryBits.writer_root, HP]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P (coefficientTask P D q) = 6 :=
    IntegralMixedCoefficientQueryBits.writer_routine P .companion .criticalCoefficient _
  have HC : isPhase .criticalCoefficient (coefficientTask P D q) :=
    IntegralMixedCoefficientQueryBits.writer_phase P .companion .criticalCoefficient _
  have HX : get P .slot15 (coefficientTask P D q) = 0 := by
    unfold coefficientTask
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_get]
    simpa only [reduceCtorEq, ite_false, HP] using hx
  exact (hm _ ((selected_iff P .criticalCoefficient _).mpr ⟨HV, HR, HC, HX⟩)).trans (coefficientTask_value P D q)

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
  apply IntegralMixedRoutineTaskBits.lower_phase P q _ (IntegralMixedRoutineTaskBits.query_birth P _ .companion .originalCoefficient q HB)
  · rw [IntegralMixedRoutineTaskBits.query_routine, hr]
    rfl
  · rw [IntegralMixedRoutineTaskBits.query_phase]
    change phase q = 26 at hp
    change 0 < phase q
    omega

abbrev LeadingMatches (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P .companion q = true → answer (leadingChild P q) = residueBits ((scalarFamily P D).leading q)

noncomputable def companionValue (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : List Bool → List Bool := (family P D).value

theorem companionValue_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = companionValue P D q := ⟨_, rfl⟩

noncomputable def companionMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D) : Machine :=
  ofTwoCalls (coefficientTask P D) (leadingChild P ∘ pairFst) (IntegralScalarGeneratorBits.chargedPost (scalarFamily P D))
    (coefficientTask_FP P a D h) (mem_FP_comp pairFst_mem_FP (leadingChild_FP P a))
    (IntegralScalarGeneratorBits.chargedPost_FP (scalarFamily P D) (scalarAccess P a D h))
    (selected P .companion) (selected_FP P a .companion) (companionValue P D)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

attribute [local irreducible] IntegralScalarGeneratorBits.chargedPost companionValue

theorem companion_result (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (hm : CoefficientMatches P D answer) (hl : LeadingMatches P D answer)
    (q : List Bool) (hq : selected P .companion q = true) :
    DependentTwoCall.result (coefficientTask P D) (leadingChild P ∘ pairFst)
      (IntegralScalarGeneratorBits.chargedPost (scalarFamily P D)) answer q = companionValue P D q := by
  have HQ := (selected_iff P .companion q).mp hq
  unfold DependentTwoCall.result
  simp only [Function.comp_apply, pairFst_pair]
  rw [coefficient_reply P D answer hm q HQ.1 HQ.2.2.2, hl q hq]
  have HE : (scalarFamily P D).toFamily.value q = companionValue P D q := by
    unfold scalarFamily IntegralScalarGeneratorBits.finFamily companionValue
    exact congrFun (PaddedIntegralGeneratorFinBits.value_eq (family P D)) q
  exact (IntegralScalarGeneratorBits.chargedPost_value (scalarFamily P D) q).trans HE

theorem companion_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : CoefficientMatches P D (fun q => residueBits (x q)))
    (hl : LeadingMatches P D (fun q => residueBits (x q))) :
    Correct (companionMachine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · exact companion_result P D _ hm hl
  · intro q hq
    have HQ := (selected_iff P .companion q).mp hq
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (coefficientTask P D q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (coefficientTask_frame P D q HQ.2.1 HQ.2.2.1).1)
  · intro q _
    obtain ⟨z, hz⟩ := companionValue_canonical P D q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
  · intro q child budget hq hc
    have HQ := (selected_iff P .companion q).mp hq
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q child hc with hleft | hright
    · rw [hleft]
      exact coefficientTask_frame P D q HQ.2.1 HQ.2.2.1
    · rw [hright]
      simpa only [Function.comp_apply, pairFst_pair] using leadingChild_frame P q HQ.2.1 HQ.2.2.1

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits
