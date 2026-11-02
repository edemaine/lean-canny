/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateProbe
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
/-! # Actual creating coordinate cuts retain their full coefficient polynomial

The immutable creating coordinate and trailing choice are restored locally.
There is deliberately no coefficient ≤ recorded-degree guard: these probes
can test the higher coefficients required for selected-degree validity.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateProbeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

def Selected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q ∧
    IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=2

theorem selected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) : FPPred (Selected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 2)))

noncomputable def preparedValue (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if Selected P D H q then value P D H (IntegralMixedRawKindBits.prepare P (family P D H) q) else []

theorem prepared_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (preparedValue P D H) := by
  have E := (evaluator P a D H h hb).precompose (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (Selected P D H q)) (selected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [preparedValue,Function.comp_apply,decide_eq_true_eq])

theorem kernel_selected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected P D H q) :
    IntegralMixedCoordinateCoefficientNative.Selected P (family P D H)
      (IntegralMixedRawKindBits.prepare P (family P D H) q) := by
  let F := family P D H
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  refine ⟨(IntegralMixedRawKindBits.prepare_valid P F q).mpr hs.1,
    IntegralMixedRawKindBits.prepare_routine P F q,IntegralMixedRawKindBits.prepare_phase P F q,?_,
    (IntegralMixedRawKindBits.prepare_context P F g q).mpr hs.2.1⟩
  change get P .slot8 (IntegralMixedRawKindBits.prepare P F q)<
    IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
  rw [IntegralMixedRawKindBits.prepare_saved]
  simp only [IntegralMixedRawKindBits.prepare_get P F g q,reduceCtorEq,ite_false,ite_true]
  exact IntegralMixedRawKindBits.coordinate_choice_lt F _ hs.2.2

theorem prepared_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : Selected P D H q) :
    preparedValue P D H q=residueBits
      (IntegralCriticalTotalSnapshotBits.integerEntry
        (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q)) (get P .coefficient q))
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [preparedValue,ite_eq_left hs,selected_value P D H _ (kernel_selected P D H q hs)]
  unfold IntegralMixedCoordinateCoefficientValue.value IntegralMixedCoordinateCoefficientSnapshot.coefficient
  have HK := IntegralMixedRawKindBits.prepare_coordinate_kind P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q hs.2.2
  rw [←HK,IntegralMixedRawKindBits.prepare_saved,IntegralMixedRawKindBits.prepare_modulus]
  simp only [IntegralMixedRawKindBits.prepare_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false]

end LeanCanny.Algebra.IntegralMixedFramedCoordinateProbeBits
