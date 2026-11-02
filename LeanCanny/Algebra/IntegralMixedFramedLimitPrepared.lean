/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedLimitProbe
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCutProbes
/-! # Full actual limit factors, including natural-index zero guards -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedLimitPreparedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedCutMatrix.coefficientMatrix IntegralMixedFramedHistoryFamilyBits.family
set_option backward.isDefEq.respectTransparency false

def Selected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q ∧
    IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=5

theorem selected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) : FPPred (Selected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 5)))

theorem currentQ_selected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) : FPPred (Selected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 5)))

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Selected P D H q then IntegralMixedFramedLimitProbeBits.value P D H
    (IntegralMixedRawKindBits.prepare P (family P D H) q) else []

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedLimitProbeBits.evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected P D H q)) (selected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [value,Function.comp_apply,decide_eq_true_eq])

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedLimitProbeBits.currentQ_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected P D H q)) (currentQ_selected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [value,Function.comp_apply,decide_eq_true_eq])

theorem full_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected P D H q) :
    value P D H q=IntegralMixedLimitCoordinateValue.value P (family P D H)
      (IntegralMixedRawKindBits.prepare P (family P D H) q) := by
  let F := family P D H
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  have HC : get P .slot8 (IntegralMixedRawKindBits.prepare P F q)<
      IntegralMixedCoordinateCoefficientTasks.choiceBound P F (IntegralMixedRawKindBits.prepare P F q) := by
    change get P .slot8 (IntegralMixedRawKindBits.prepare P F q)<
      IntegralMixedCoordinateTrailing.ChoiceBound
        (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
        (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
    rw [IntegralMixedRawKindBits.prepare_saved]
    simp only [IntegralMixedRawKindBits.prepare_get P F g q,reduceCtorEq,ite_false,ite_true]
    exact IntegralMixedRawKindBits.limit_choice_lt F _ hs.2.2
  rw [value,ite_eq_left hs]
  unfold IntegralMixedFramedLimitProbeBits.value
  by_cases hN : IntegralMixedLimitCoordinateNative.Selected P F (IntegralMixedRawKindBits.prepare P F q)
  · exact ite_eq_left hN
  · rw [ite_eq_right hN]
    by_cases hk : get P .coefficient (IntegralMixedRawKindBits.prepare P F q)≤get P .slot8 (IntegralMixedRawKindBits.prepare P F q)
    · apply (IntegralMixedLimitCoordinateNative.value_outside P F _ HC hk ?_).symm
      intro hl
      exact hN ⟨(IntegralMixedRawKindBits.prepare_valid P F q).mpr hs.1,
        IntegralMixedRawKindBits.prepare_routine P F q,IntegralMixedRawKindBits.prepare_phase P F q,
        (IntegralMixedRawKindBits.prepare_context P F g q).mpr hs.2.1,HC,hk,hl⟩
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
          ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q)) (get P .coefficient q))
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [full_value P D H q hs]
  unfold IntegralMixedLimitCoordinateValue.value IntegralMixedLimitCoordinateSnapshot.coefficient
  rw [matrix_eq]
  have HK := IntegralMixedRawKindBits.prepare_limit_kind P (family P D H) (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q hs.2.2
  rw [←HK,IntegralMixedRawKindBits.prepare_saved,IntegralMixedRawKindBits.prepare_modulus]
  simp only [IntegralMixedRawKindBits.prepare_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false]

end LeanCanny.Algebra.IntegralMixedFramedLimitPreparedBits
