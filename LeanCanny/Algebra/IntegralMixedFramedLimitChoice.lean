/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoicePrepared
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCutProbes
/-! # Full lower-choice limit factors of the actual parent -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedLimitChoiceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedCutMatrix.coefficientMatrix IntegralMixedFramedHistoryFamilyBits.family
set_option backward.isDefEq.respectTransparency false

abbrev Selected := IntegralMixedFramedChoicePreparedBits.Selected 5

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Selected P D H q then IntegralMixedFramedLimitProbeBits.value P D H
    (IntegralMixedRawKindChoiceBits.query P (family P D H) q) else []

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedLimitProbeBits.currentQ_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindChoiceBits.query P (family P D H))
    (IntegralMixedRawKindChoiceBits.query_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected P D H q))
    (IntegralMixedFramedChoicePreparedBits.selected_FP 5 P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [value,Function.comp_apply,decide_eq_true_eq])

theorem full_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected P D H q) :
    value P D H q=IntegralMixedLimitCoordinateValue.value P (family P D H)
      (IntegralMixedRawKindChoiceBits.query P (family P D H) q) := by
  let F := family P D H
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  have HC : get P .slot8 (IntegralMixedRawKindChoiceBits.query P F q)<
      IntegralMixedCoordinateCoefficientTasks.choiceBound P F (IntegralMixedRawKindChoiceBits.query P F q) := by
    change get P .slot8 (IntegralMixedRawKindChoiceBits.query P F q)<
      IntegralMixedCoordinateTrailing.ChoiceBound
        (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
        (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
    rw [IntegralMixedRawKindChoiceBits.query_saved]
    simp only [IntegralMixedRawKindChoiceBits.query_get P F g q,reduceCtorEq,ite_false,ite_true]
    exact (min_le_right _ _).trans_lt (IntegralMixedRawKindBits.limit_choice_lt F _ hs.2.2.1)
  rw [value,ite_eq_left hs]
  unfold IntegralMixedFramedLimitProbeBits.value
  by_cases hN : IntegralMixedLimitCoordinateNative.Selected P F (IntegralMixedRawKindChoiceBits.query P F q)
  · exact ite_eq_left hN
  · rw [ite_eq_right hN]
    by_cases hk : get P .coefficient (IntegralMixedRawKindChoiceBits.query P F q)≤get P .slot8 (IntegralMixedRawKindChoiceBits.query P F q)
    · apply (IntegralMixedLimitCoordinateNative.value_outside P F _ HC hk ?_).symm
      intro hl
      exact hN ⟨(IntegralMixedRawKindChoiceBits.query_valid P F q).mpr hs.1,
        IntegralMixedRawKindChoiceBits.query_routine P F q,IntegralMixedRawKindChoiceBits.query_phase P F q,
        (IntegralMixedRawKindChoiceBits.query_context P F g q).mpr hs.2.1,HC,hk,hl⟩
    · exact (IntegralMixedLimitCoordinateNative.value_above P F _ HC hk).symm


private theorem matrix_eq (F : IntegralMixedCutSource.Family) (key : List Bool) (j c k : ℕ) :
    IntegralMixedLimitCoordinateSnapshot.matrix F key j c k=
      IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key)
        (IntegralMixedRawKindBits.limitKind F key j c) k := by
  unfold IntegralMixedLimitCoordinateSnapshot.matrix IntegralMixedCutMatrix.coefficientMatrix
    IntegralMixedLimitCoordinateSnapshot.factor IntegralMixedRelativeCuts.factor IntegralMixedRawKindBits.limitKind
  rfl

theorem entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected P D H q) :
    value P D H q=residueBits
      (IntegralCriticalTotalSnapshotBits.integerEntry
        (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
            ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q)) (IntegralMixedRawKindChoiceBits.requested P q)) (get P .coefficient q))
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [full_value P D H q hs]
  unfold IntegralMixedLimitCoordinateValue.value IntegralMixedLimitCoordinateSnapshot.coefficient
  rw [matrix_eq]
  rw [IntegralMixedRawKindChoiceBits.query_saved,IntegralMixedRawKindChoiceBits.query_modulus]
  simp only [IntegralMixedRawKindChoiceBits.query_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false,ite_true]
  unfold IntegralMixedRawKindChoiceBits.selected
  rw [←IntegralMixedCutChoiceFamilyBits.limit_kind (family P D H) _ _ hs.2.2.1]

end LeanCanny.Algebra.IntegralMixedFramedLimitChoiceBits
