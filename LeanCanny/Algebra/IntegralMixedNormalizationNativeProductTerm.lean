/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationProductQueries
public import LeanCanny.Computation.NativeTwoCallBranch
/-! # A native inverse/raw product term uses two current matrix replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev InverseMatrixMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .frozenConstant q → answer q = inverseMatrixValue P F q

def productAxes (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  get P .row q < matrixDimension P F q ∧ get P .col q < matrixDimension P F q ∧ get P .target q < matrixDimension P F q

noncomputable def selected12 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P .frozenLower q && decide (productAxes P F q)

theorem selected12_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected12 P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a .frozenLower)).and
    (((get_binary P a .row).lt (matrixDimension_binary P a F h)).and
      (((get_binary P a .col).lt (matrixDimension_binary P a F h)).and
        ((get_binary P a .target).lt (matrixDimension_binary P a F h))))).flag_mem_FP
    (fun q => by cases hb : selected P .frozenLower q <;> simp [selected12, productAxes, hb])

theorem selected12_iff (P : Parameters) (F : Family) (q : List Bool) : selected12 P F q = true ↔
    (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .frozenLower q) ∧ productAxes P F q := by
  simp only [selected12, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

theorem productTermValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = productTermValue P F q := ⟨_, rfl⟩

theorem productTerm_result (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool)
    (hh : get P .target q < matrixDimension P F q) (ht : get P .col q < matrixDimension P F q)
    (hi : answer (productLeft P q) = inverseMatrixValue P F (productLeft P q))
    (hr : answer (productRight P (pair q (answer (productLeft P q)))) =
      rawCutValue P F (productRight P (pair q (answer (productLeft P q))))) :
    DependentTwoCall.result (productLeft P) (productRight P) (multiplyPost P) answer q = productTermValue P F q := by
  unfold DependentTwoCall.result
  rw [hr, hi, productLeft_value, productRight_value P F q _ hh ht]
  simp only [multiplyPost, pairFst_pair, pairSnd_pair, productTermValue, Int.cast_mul]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  exact ArithmeticBits.mulMod_residueBits _ _ _

noncomputable def stage12 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofTwoCalls (productLeft P) (productRight P) (multiplyPost P) (productLeft_FP P a) (productRight_FP P a) (multiplyPost_FP P a)
    (selected12 P F) (selected12_FP P a F h) (productTermValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

attribute [local irreducible] productTermValue

theorem correct12 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (x : (q : List Bool) → ZMod (modulus P q))
    (hi : InverseMatrixMatches P F (fun q => residueBits (x q))) (hr : RawMatches P F (fun q => residueBits (x q))) :
    Correct (stage12 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · intro q hq
    have H := (selected12_iff P F q).mp hq
    apply productTerm_result P F _ q H.2.2.2 H.2.2.1
    · apply hi
      · unfold IntegralMixedVirtualCaps.valid productLeft
        rw [IntegralMixedValueFieldQuery.query_birth, IntegralMixedValueFieldQuery.query_root]
        exact H.1.1
      · exact IntegralMixedValueFieldQuery.query_routine P id .normalization .frozenConstant .col _ q
      · exact IntegralMixedValueFieldQuery.query_phase P id .normalization .frozenConstant .col _ q
    · apply hr
      · unfold IntegralMixedVirtualCaps.valid productRight
        rw [IntegralMixedValueFieldQuery.query_birth, IntegralMixedValueFieldQuery.query_root, pairFst_pair]
        exact H.1.1
      · exact IntegralMixedValueFieldQuery.query_routine P pairFst .rawFactor .companion .row _ _
      · exact IntegralMixedValueFieldQuery.query_phase P pairFst .rawFactor .companion .row _ _
  · intro q _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (productLeft P q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (IntegralMixedValueFieldQuery.query_root P id .normalization .frozenConstant .col _ q))
  · intro q _
    obtain ⟨z, hz⟩ := productTermValue_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact (residueBits_length_le _ _).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
  · intro q c budget hq hc
    have H := (selected12_iff P F q).mp hq
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q c hc with hl | hr
    · rw [hl]
      have HP := H.1.2.2
      change phase q = 12 at HP
      exact productLeft_frame P q H.1.2.1 (by omega)
    · rw [hr]
      exact productRight_frame P q _ H.1.2.1

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
