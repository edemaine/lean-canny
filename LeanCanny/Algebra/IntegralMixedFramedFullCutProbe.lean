/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateProbePrepared
public import LeanCanny.Algebra.IntegralMixedFramedExceptionalPrepared
public import LeanCanny.Algebra.IntegralMixedFramedLimitPrepared
/-! # Native full relative-factor coefficients for all four creating tags

The reader exposes the literal coefficient matrix at the same saved
parent, before the recorded-degree truncation used by normalization.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutProbeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

def Active (P : Parameters) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedVirtualContextBits.context P q
theorem active_FP (P : Parameters) (a : Access P) : FPPred (Active P) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and (IntegralMixedVirtualContextBits.context_FP P a)

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  if Active P q then residueBits
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q)) (get P .coefficient q))
      (get P .row q) (get P .col q) : ZMod (modulus P q)) else []

private theorem coordinate_evaluator_currentQ (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (IntegralMixedFramedCoordinateProbeBits.preparedValue P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  have HP : FPPred (IntegralMixedFramedCoordinateProbeBits.Selected P D H) :=
    (IntegralMixedVirtualCaps.valid_FP P a).and ((IntegralMixedVirtualContextBits.context_FP P a).and
      (HT.eq (BinaryFn.const 2)))
  have E := (IntegralMixedFramedCoordinateProbeBits.currentQ_evaluator P a D H h hb).precompose
    (IntegralMixedRawKindBits.prepare P (family P D H))
    (IntegralMixedRawKindBits.prepare_FP P a (family P D H)
      (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization))
  exact (SpaceFunction.branch (fun q=>decide (IntegralMixedFramedCoordinateProbeBits.Selected P D H q)) HP.flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
      funext q
      simp only [IntegralMixedFramedCoordinateProbeBits.preparedValue,Function.comp_apply,decide_eq_true_eq])

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  have EC:=IntegralMixedFramedCoordinateProbeBits.prepared_evaluator P a D H h hb
  have ES:=IntegralMixedFramedExceptionalPreparedBits.squarefree_evaluator P a D H h hb
  have EV:=IntegralMixedFramedExceptionalPreparedBits.value_evaluator P a D H h hb
  have EL:=IntegralMixedFramedLimitPreparedBits.evaluator P a D H h hb
  have E := SpaceFunction.branch (fun q=>decide (Active P q)) (active_FP P a).flag_mem_FP
    (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=2))
      (HT.eq (BinaryFn.const 2)).flag_mem_FP EC
      (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=3))
        (HT.eq (BinaryFn.const 3)).flag_mem_FP ES
        (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=4))
          (HT.eq (BinaryFn.const 4)).flag_mem_FP EV EL))) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply E.congr
  funext q
  simp only [value,decide_eq_true_eq]
  by_cases ha : Active P q
  · simp only [ha,ite_true]
    split_ifs with hc hs hv
    · exact IntegralMixedFramedCoordinateProbeBits.prepared_value P D H q ⟨ha.1,ha.2,hc⟩
    · exact IntegralMixedFramedExceptionalPreparedBits.squarefree_entry P D H q ⟨ha.1,ha.2,hs⟩
    · exact IntegralMixedFramedExceptionalPreparedBits.value_entry P D H q ⟨ha.1,ha.2,hv⟩
    · have HB:=IntegralMixedRawKindBits.tag_bounds (family P D H) (IntegralMixedVirtualTaskBits.saved P q)
      exact IntegralMixedFramedLimitPreparedBits.entry P D H q ⟨ha.1,ha.2,by omega⟩
  · simp only [ha,ite_false]

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization).tag.comp
      (IntegralMixedVirtualTaskBits.saved_FP P a)
  have EC:=coordinate_evaluator_currentQ P a D H h hb
  have ES:=IntegralMixedFramedExceptionalPreparedBits.currentQ_squarefree_evaluator P a D H h hb
  have EV:=IntegralMixedFramedExceptionalPreparedBits.currentQ_value_evaluator P a D H h hb
  have EL:=IntegralMixedFramedLimitPreparedBits.currentQ_evaluator P a D H h hb
  have E := SpaceFunction.branch (fun q=>decide (Active P q)) (active_FP P a).flag_mem_FP
    (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=2))
      (HT.eq (BinaryFn.const 2)).flag_mem_FP EC
      (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=3))
        (HT.eq (BinaryFn.const 3)).flag_mem_FP ES
        (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=4))
          (HT.eq (BinaryFn.const 4)).flag_mem_FP EV EL))) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply E.congr
  funext q
  simp only [value,decide_eq_true_eq]
  by_cases ha : Active P q
  · simp only [ha,ite_true]
    split_ifs with hc hs hv
    · exact IntegralMixedFramedCoordinateProbeBits.prepared_value P D H q ⟨ha.1,ha.2,hc⟩
    · exact IntegralMixedFramedExceptionalPreparedBits.squarefree_entry P D H q ⟨ha.1,ha.2,hs⟩
    · exact IntegralMixedFramedExceptionalPreparedBits.value_entry P D H q ⟨ha.1,ha.2,hv⟩
    · have HB:=IntegralMixedRawKindBits.tag_bounds (family P D H) (IntegralMixedVirtualTaskBits.saved P q)
      exact IntegralMixedFramedLimitPreparedBits.entry P D H q ⟨ha.1,ha.2,by omega⟩
  · simp only [ha,ite_false]

end LeanCanny.Algebra.IntegralMixedFramedFullCutProbeBits
