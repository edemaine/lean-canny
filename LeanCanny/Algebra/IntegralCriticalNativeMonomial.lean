/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native monomial-factor branch over actual coefficient and height leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeMonomialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalFlatActualLow.source F
noncomputable abbrev access (F : Scripts) (h : Controls F) := IntegralCriticalFlatActualLow.access F h
noncomputable abbrev program (F : Scripts) (h : Controls F) := IntegralCriticalFlatGenericMonomialBits.program F.toParameters (source F) (access F h)
noncomputable abbrev input (F : Scripts) := IntegralCriticalFlatGenericMonomialBits.input F.toParameters (source F)

theorem certificates (F : Scripts) (h : Controls F) :
    (program F h).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program F h).certificates (IntegralCriticalFlatGenericMonomialBits.controls F.toParameters h.task.toAccess (source F) (access F h)
    (IntegralCriticalFlatActualLow.denominator_FP F h))

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofPreparedSingleCall (program F h) (certificates F h) (input F)
    (IntegralCriticalFlatGenericMonomialBits.input_FP F.toParameters h.task.toAccess (source F) (access F h))
    (selected F .monomialFactor) (selected_FP F h .monomialFactor) (IntegralCriticalActualFactorModel.monomial F)
    (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem coefficient_match (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (pairFst z)) :
    answer F x (IntegralCriticalFlatGenericMonomialBits.coefficientTask F.toParameters z) =
      IntegralCriticalActualMonomialReplies.answer F (IntegralCriticalFlatGenericMonomialBits.coefficientTask F.toParameters z) := by
  unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
  split_ifs
  · rw [matches_matrix F x hm .derivativeCoefficient (by decide) z hv]
    unfold IntegralCriticalActualMonomialReplies.answer
    rw [IntegralCriticalFlatMatrixQuery.writer_phase]
    rfl
  · rw [matches_matrix F x hm .originalCoefficient (by decide) z hv]
    unfold IntegralCriticalActualMonomialReplies.answer
    rw [IntegralCriticalFlatMatrixQuery.writer_phase]
    rfl

theorem query_eq (F : Scripts) (h : Controls F) (q : List Bool) :
    (program F h).query (input F q) =
      if IntegralMonomialTermBits.position (input F q) = 0 then
        IntegralCriticalFlatGenericMonomialBits.coefficientTask F.toParameters (IntegralMonomialTermBits.coefficientQuery (input F q))
      else IntegralCriticalFlatFactorQuery.writer F.toParameters .clearedHeight (IntegralMonomialTermBits.heightQuery (input F q)) := rfl

theorem query_match (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    answer F x ((program F h).query (input F q)) = IntegralCriticalActualMonomialReplies.answer F ((program F h).query (input F q)) := by
  rw [query_eq]
  split_ifs
  · exact coefficient_match F x hm _ (by
      rw [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent]
      exact hv)
  · rw [matches_factor F x hm .clearedHeight (by decide)
      (IntegralMonomialTermBits.heightQuery (input F q)) (by
        rw [IntegralCriticalFlatGenericMonomialBits.heightQuery_parent]
        exact hv)]
    unfold IntegralCriticalActualMonomialReplies.answer
    rw [IntegralCriticalFlatFactorQuery.writer_phase]
    rfl

theorem requests_frame (F : Scripts) (h : Controls F) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .monomialFactor q) (hc : ((program F h).controller.prepare (input F)).Requests reply budget q c) : Frame F q c := by
  have H0 := (RecursiveController.Controller.prepare_requests_iff (program F h).controller (input F) reply budget q c).mp hc
  have H1 := ((program F h).requests_iff reply (fun _ => budget q) (input F q) c).mp H0
  apply Eq.mpr (congrArg (Frame F q) H1.2)
  rw [query_eq]
  change phase q = 3 at hp
  split_ifs
  · unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
    split_ifs
    · simpa only [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent] using frame_matrix F .derivativeCoefficient
        (IntegralMonomialTermBits.coefficientQuery (input F q)) (by
          rw [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent]
          change 1 < phase q
          omega)
    · simpa only [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent] using frame_matrix F .originalCoefficient
        (IntegralMonomialTermBits.coefficientQuery (input F q)) (by
          rw [IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent]
          change 0 < phase q
          omega)
  · simpa only [IntegralCriticalFlatGenericMonomialBits.heightQuery_parent] using frame_factor F .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input F q)) (by
        rw [IntegralCriticalFlatGenericMonomialBits.heightQuery_parent]
        change 2 < phase q
        omega)

theorem value_at (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F h).value (answer F x) (input F q) = IntegralCriticalActualFactorModel.monomial F q :=
  (single_value_congr_at (program F h) (answer F x) (IntegralCriticalActualMonomialReplies.answer F) (input F q)
    (fun _ => query_match F h x hm q hv)).trans (IntegralCriticalActualMonomialReplies.monomial_value F h q)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply prepared_correct_of_frame F h .monomialFactor (program F h) (certificates F h) (input F)
    (IntegralCriticalFlatGenericMonomialBits.input_FP F.toParameters h.task.toAccess (source F) (access F h))
    (IntegralCriticalActualFactorModel.monomial F) x
  · intro q hq
    exact value_at F h x hm q ((selected_iff F .monomialFactor q).mp hq).1
  · intro q c budget hq hc
    exact requests_frame F h (answer F x) budget q c ((selected_iff F .monomialFactor q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeMonomialBits
