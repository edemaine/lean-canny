/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindChoiceQuery
public import LeanCanny.Algebra.IntegralMixedCutChoiceFamily
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCutProbes
/-! # Native full coefficients at a lower finite choice of the same parent

The creating script is untouched. Local slot8 probes select all finite
choices up to the actual creating choice, preserving the original sweep,
coordinate, coefficient algebra, joint tuple and caller modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoicePreparedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

def Selected (tag : ℕ) (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q ∧
    IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=tag ∧
    IntegralMixedRawKindChoiceBits.requested P q≤IntegralMixedRawKindBits.choice (family P D H) (IntegralMixedVirtualTaskBits.saved P q)
theorem selected_FP (tag : ℕ) (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) : FPPred (Selected tag P D H) := by
  let k:=IntegralMixedFramedNormalizationBits.kind P a D H h.normalization
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    k.tag.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    ((HT.eq (BinaryFn.const tag)).and ((get_binary P a .slot8).le (k.choice.comp (IntegralMixedVirtualTaskBits.saved_FP P a)))))

noncomputable def coordinate (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Selected 2 P D H q then IntegralMixedFramedCoordinateProbeBits.value P D H
    (IntegralMixedRawKindChoiceBits.query P (family P D H) q) else []
theorem coordinate_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (coordinate P D H) := by
  have E := (IntegralMixedFramedCoordinateProbeBits.currentQ_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindChoiceBits.query P (family P D H))
    (IntegralMixedRawKindChoiceBits.query_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected 2 P D H q)) (selected_FP 2 P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [coordinate,Function.comp_apply,decide_eq_true_eq])

theorem coordinate_kernel (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected 2 P D H q) :
    IntegralMixedCoordinateCoefficientNative.Selected P (family P D H)
      (IntegralMixedRawKindChoiceBits.query P (family P D H) q) := by
  let F:=family P D H
  let g:=IntegralMixedFramedHistoryFamilyBits.geometry P D H
  refine ⟨(IntegralMixedRawKindChoiceBits.query_valid P F q).mpr hs.1,
    IntegralMixedRawKindChoiceBits.query_routine P F q,IntegralMixedRawKindChoiceBits.query_phase P F q,?_,(IntegralMixedRawKindChoiceBits.query_context P F g q).mpr hs.2.1⟩
  change get P .slot8 (IntegralMixedRawKindChoiceBits.query P F q)<
    IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
  rw [IntegralMixedRawKindChoiceBits.query_saved]
  simp only [IntegralMixedRawKindChoiceBits.query_get P F g q,reduceCtorEq,ite_false,ite_true]
  exact (min_le_right _ _).trans_lt (IntegralMixedRawKindBits.coordinate_choice_lt F _ hs.2.2.1)

theorem coordinate_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected 2 P D H q) :
    coordinate P D H q=residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).birth_bound _) ((family P D H).rule _)
        (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P q)) (get P .coefficient q))
      (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [coordinate,ite_eq_left hs]
  rw [IntegralMixedFramedCoordinateProbeBits.selected_value P D H _ (coordinate_kernel P D H q hs)]
  unfold IntegralMixedCoordinateCoefficientValue.value IntegralMixedCoordinateCoefficientSnapshot.coefficient
  rw [IntegralMixedRawKindChoiceBits.query_saved,IntegralMixedRawKindChoiceBits.query_modulus]
  simp only [IntegralMixedRawKindChoiceBits.query_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false,ite_true]
  unfold IntegralMixedRawKindChoiceBits.selected
  rw [←IntegralMixedCutChoiceFamilyBits.coordinate_kind (family P D H) _ _ hs.2.2.1]

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Selected 4 P D H q then IntegralMixedFramedExceptionalProbeBits.value P D H
    (IntegralMixedRawKindChoiceBits.query P (family P D H) q) else []
theorem value_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedExceptionalProbeBits.currentQ_value_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindChoiceBits.query P (family P D H))
    (IntegralMixedRawKindChoiceBits.query_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected 4 P D H q)) (selected_FP 4 P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [value,Function.comp_apply,decide_eq_true_eq])

theorem value_kernel (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected 4 P D H q) :
    IntegralMixedValueCoefficientNative.Selected P (family P D H)
      (IntegralMixedRawKindChoiceBits.query P (family P D H) q) := by
  let F:=family P D H
  let g:=IntegralMixedFramedHistoryFamilyBits.geometry P D H
  refine ⟨(IntegralMixedRawKindChoiceBits.query_valid P F q).mpr hs.1,
    IntegralMixedRawKindChoiceBits.query_routine P F q,IntegralMixedRawKindChoiceBits.query_phase P F q,?_⟩
  change get P .slot8 (IntegralMixedRawKindChoiceBits.query P F q)<
    IntegralMixedValueTrailing.ChoiceBound (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
  rw [IntegralMixedRawKindChoiceBits.query_saved]
  simp only [IntegralMixedRawKindChoiceBits.query_get P F g q,reduceCtorEq,ite_false,ite_true]
  exact (min_le_right _ _).trans_lt (IntegralMixedRawKindBits.value_choice_lt F _ hs.2.2.1)

theorem value_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected 4 P D H q) :
    value P D H q=residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).birth_bound _) ((family P D H).rule _)
        (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P q)) (get P .coefficient q))
      (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [value,ite_eq_left hs]
  unfold IntegralMixedFramedExceptionalProbeBits.value
  rw [ite_eq_left ⟨value_kernel P D H q hs,(IntegralMixedRawKindChoiceBits.query_context P (family P D H) (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q).mpr hs.2.1⟩]
  unfold IntegralMixedValueCoefficientValue.value IntegralMixedValueCoefficientSnapshot.coefficient
  rw [IntegralMixedRawKindChoiceBits.query_saved,IntegralMixedRawKindChoiceBits.query_modulus]
  simp only [IntegralMixedRawKindChoiceBits.query_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false,ite_true]
  unfold IntegralMixedRawKindChoiceBits.selected
  rw [←IntegralMixedCutChoiceFamilyBits.value_kind (family P D H) _ _ hs.2.2.1]

noncomputable def squarefree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Selected 3 P D H q then IntegralMixedFramedExceptionalProbeBits.squarefree P D H
    (IntegralMixedRawKindChoiceBits.query P (family P D H) q) else []
theorem squarefree_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (squarefree P D H) := by
  have E := (IntegralMixedFramedExceptionalProbeBits.currentQ_squarefree_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindChoiceBits.query P (family P D H))
    (IntegralMixedRawKindChoiceBits.query_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected 3 P D H q)) (selected_FP 3 P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [squarefree,Function.comp_apply,decide_eq_true_eq])

theorem squarefree_kernel (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected 3 P D H q) :
    IntegralMixedSquarefreeCoefficientNative.Selected P (family P D H)
      (IntegralMixedRawKindChoiceBits.query P (family P D H) q) := by
  let F:=family P D H
  let g:=IntegralMixedFramedHistoryFamilyBits.geometry P D H
  refine ⟨(IntegralMixedRawKindChoiceBits.query_valid P F q).mpr hs.1,
    IntegralMixedRawKindChoiceBits.query_routine P F q,IntegralMixedRawKindChoiceBits.query_phase P F q,(IntegralMixedRawKindChoiceBits.query_context P F g q).mpr hs.2.1,?_⟩
  change get P .slot8 (IntegralMixedRawKindChoiceBits.query P F q)<
    IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindChoiceBits.query P F q)))
  rw [IntegralMixedRawKindChoiceBits.query_saved]
  simp only [IntegralMixedRawKindChoiceBits.query_get P F g q,reduceCtorEq,ite_false,ite_true]
  exact (min_le_right _ _).trans_lt (IntegralMixedRawKindBits.squarefree_choice_lt F _ hs.2.2.1)

theorem squarefree_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected 3 P D H q) :
    squarefree P D H q=residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).birth_bound _) ((family P D H).rule _)
        (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P q)) (get P .coefficient q))
      (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [squarefree,ite_eq_left hs]
  unfold IntegralMixedFramedExceptionalProbeBits.squarefree
  rw [ite_eq_left (squarefree_kernel P D H q hs)]
  unfold IntegralMixedSquarefreeCoefficientValue.value IntegralMixedSquarefreeCoefficientSnapshot.coefficient
  rw [IntegralMixedRawKindChoiceBits.query_saved,IntegralMixedRawKindChoiceBits.query_modulus]
  simp only [IntegralMixedRawKindChoiceBits.query_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false,ite_true]
  unfold IntegralMixedRawKindChoiceBits.selected
  rw [←IntegralMixedCutChoiceFamilyBits.squarefree_kind (family P D H) _ _ hs.2.2.1]

end LeanCanny.Algebra.IntegralMixedFramedChoicePreparedBits
