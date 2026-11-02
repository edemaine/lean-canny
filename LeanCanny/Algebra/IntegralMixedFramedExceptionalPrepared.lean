/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedExceptionalProbes
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCutProbes
/-! # Full exceptional factors after restoring the actual creating choice

No recorded scalar-degree truncation is applied. In particular these
readers expose higher coefficients for exact selected-degree tests.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedExceptionalPreparedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedCutMatrix.coefficientMatrix IntegralMixedFramedHistoryFamilyBits.family
set_option backward.isDefEq.respectTransparency false

def valueSelected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q ∧
    IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=4
theorem valueSelected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) : FPPred (valueSelected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 4)))
theorem currentQ_valueSelected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) : FPPred (valueSelected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 4)))
noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if valueSelected P D H q then IntegralMixedFramedExceptionalProbeBits.value P D H
    (IntegralMixedRawKindBits.prepare P (family P D H) q) else []
theorem value_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedExceptionalProbeBits.value_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (valueSelected P D H q)) (valueSelected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [value,Function.comp_apply,decide_eq_true_eq])
theorem currentQ_value_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedExceptionalProbeBits.currentQ_value_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (valueSelected P D H q)) (currentQ_valueSelected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [value,Function.comp_apply,decide_eq_true_eq])
theorem value_kernel (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : valueSelected P D H q) :
    IntegralMixedValueCoefficientNative.Selected P (family P D H)
      (IntegralMixedRawKindBits.prepare P (family P D H) q) := by
  let F := family P D H
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  refine ⟨(IntegralMixedRawKindBits.prepare_valid P F q).mpr hs.1,
    IntegralMixedRawKindBits.prepare_routine P F q,IntegralMixedRawKindBits.prepare_phase P F q,?_⟩
  change get P .slot8 (IntegralMixedRawKindBits.prepare P F q)<
    IntegralMixedValueTrailing.ChoiceBound (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
  rw [IntegralMixedRawKindBits.prepare_saved]
  simp only [IntegralMixedRawKindBits.prepare_get P F g q,reduceCtorEq,ite_false,ite_true]
  exact IntegralMixedRawKindBits.value_choice_lt F _ hs.2.2

theorem value_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : valueSelected P D H q) :
    value P D H q=residueBits
      (IntegralCriticalTotalSnapshotBits.integerEntry
        (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q)) (get P .coefficient q))
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [value,ite_eq_left hs]
  unfold IntegralMixedFramedExceptionalProbeBits.value
  rw [ite_eq_left ⟨value_kernel P D H q hs,(IntegralMixedRawKindBits.prepare_context P (family P D H) (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q).mpr hs.2.1⟩]
  unfold IntegralMixedValueCoefficientValue.value IntegralMixedValueCoefficientSnapshot.coefficient
  have HK := IntegralMixedRawKindBits.prepare_value_kind P (family P D H) (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q hs.2.2
  rw [←HK,IntegralMixedRawKindBits.prepare_saved,IntegralMixedRawKindBits.prepare_modulus]
  simp only [IntegralMixedRawKindBits.prepare_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false]

def squarefreeSelected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q ∧
    IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=3
theorem squarefreeSelected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) : FPPred (squarefreeSelected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 3)))
theorem currentQ_squarefreeSelected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) : FPPred (squarefreeSelected P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
    (HT.eq (BinaryFn.const 3)))
noncomputable def squarefree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if squarefreeSelected P D H q then IntegralMixedFramedExceptionalProbeBits.squarefree P D H
    (IntegralMixedRawKindBits.prepare P (family P D H) q) else []
theorem squarefree_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (squarefree P D H) := by
  have E := (IntegralMixedFramedExceptionalProbeBits.squarefree_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (squarefreeSelected P D H q)) (squarefreeSelected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [squarefree,Function.comp_apply,decide_eq_true_eq])
theorem currentQ_squarefree_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (squarefree P D H) := by
  have E := (IntegralMixedFramedExceptionalProbeBits.currentQ_squarefree_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (squarefreeSelected P D H q)) (currentQ_squarefreeSelected_FP P a D H h).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [squarefree,Function.comp_apply,decide_eq_true_eq])
theorem squarefree_kernel (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : squarefreeSelected P D H q) :
    IntegralMixedSquarefreeCoefficientNative.Selected P (family P D H)
      (IntegralMixedRawKindBits.prepare P (family P D H) q) := by
  let F := family P D H
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  refine ⟨(IntegralMixedRawKindBits.prepare_valid P F q).mpr hs.1,
    IntegralMixedRawKindBits.prepare_routine P F q,IntegralMixedRawKindBits.prepare_phase P F q,(IntegralMixedRawKindBits.prepare_context P F g q).mpr hs.2.1,?_⟩
  change get P .slot8 (IntegralMixedRawKindBits.prepare P F q)<
    IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
  rw [IntegralMixedRawKindBits.prepare_saved]
  simp only [IntegralMixedRawKindBits.prepare_get P F g q,reduceCtorEq,ite_false,ite_true]
  exact IntegralMixedRawKindBits.squarefree_choice_lt F _ hs.2.2

theorem squarefree_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : squarefreeSelected P D H q) :
    squarefree P D H q=residueBits
      (IntegralCriticalTotalSnapshotBits.integerEntry
        (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q)) (get P .coefficient q))
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [squarefree,ite_eq_left hs]
  unfold IntegralMixedFramedExceptionalProbeBits.squarefree
  rw [ite_eq_left (squarefree_kernel P D H q hs)]
  unfold IntegralMixedSquarefreeCoefficientValue.value IntegralMixedSquarefreeCoefficientSnapshot.coefficient
  have HK := IntegralMixedRawKindBits.prepare_squarefree_kind P (family P D H) (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q hs.2.2
  change (family P D H).kind (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P (family P D H) q))=
    IntegralMixedSquarefreeCoefficientSnapshot.kind (family P D H)
      (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P (family P D H) q))
      (get P .slot13 (IntegralMixedRawKindBits.prepare P (family P D H) q))
      (get P .slot8 (IntegralMixedRawKindBits.prepare P (family P D H) q)) at HK
  rw [←HK,IntegralMixedRawKindBits.prepare_saved,IntegralMixedRawKindBits.prepare_modulus]
  simp only [IntegralMixedRawKindBits.prepare_get P (family P D H)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) q,reduceCtorEq,ite_false]

end LeanCanny.Algebra.IntegralMixedFramedExceptionalPreparedBits
