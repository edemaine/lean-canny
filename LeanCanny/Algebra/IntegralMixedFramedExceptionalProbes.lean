/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
public import LeanCanny.Computation.SingleCallSpace
/-! # Untruncated value and squarefree coefficients from the actual native model

These programs call the existing full factor stages, before the recorded
degree guard of normalization. Every charged reply comes from the proved
complete native model. No factor or coefficient evaluator is an input.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedExceptionalProbeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

def ValueSelected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedValueCoefficientNative.Selected P (family P D H) q ∧ IntegralMixedVirtualContextBits.context P q
theorem valueSelected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) : FPPred (ValueSelected P D H) :=
  (IntegralMixedValueCoefficientNative.selected_FP P a (family P D H)
    (IntegralMixedFramedNormalizationBits.input P a D H h.normalization)).and (IntegralMixedVirtualContextBits.context_FP P a)

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if ValueSelected P D H q then IntegralMixedValueCoefficientValue.value P (family P D H) q else []
noncomputable def squarefree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if IntegralMixedSquarefreeCoefficientNative.Selected P (family P D H) q then
    IntegralMixedSquarefreeCoefficientValue.value P (family P D H) q else []

theorem value_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedNativeBits.machine P a D H h).model
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  have HE := IntegralMixedFramedNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HR:=IntegralMixedFramedNativeBits.raw_matches P a D H h answer hm
  have own:=IntegralMixedRawDispatcherBits.valueFactor_matches P a F I
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization)
    (IntegralMixedFramedNormalizationBits.degree P a D H h.normalization)
    (IntegralMixedFramedHeaderBits.routing P D)
    (IntegralMixedFramedNormalizationBits.routingAccess P a D H h.normalization) answer HR
  have EI := (IntegralMixedValueCoefficientNative.program P F).value_evaluator
    (IntegralMixedValueCoefficientNative.controls P a F I) answer HE
  have ES:=SpaceFunction.branch (fun q=>decide (ValueSelected P D H q)) (valueSelected_FP P a D H h).flag_mem_FP
    EI (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q=>by
    by_cases hs : ValueSelected P D H q
    · simp only [value,hs,decide_true,ite_true]
      apply IntegralMixedValueCoefficientNative.value_at P F g answer q hs.1.1
      intro hl
      apply own
      refine ⟨IntegralMixedValueCoefficientNative.child_selected P F g q hs.1 hl,?_⟩
      unfold IntegralMixedVirtualContextBits.context
      simpa only [IntegralMixedVirtualContextBits.context,
        IntegralMixedValueCoefficientTasks.query_get P F g q hs.1.1 hl,reduceCtorEq,ite_false] using hs.2
    · simp only [value,hs,decide_false,Bool.false_eq_true,ite_false])

theorem squarefree_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (squarefree P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedNativeBits.machine P a D H h).model
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  have HE := IntegralMixedFramedNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HR:=IntegralMixedFramedNativeBits.raw_matches P a D H h answer hm
  have own:=IntegralMixedRawDispatcherBits.squarefreeFactor_matches P a F I
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization)
    (IntegralMixedFramedNormalizationBits.degree P a D H h.normalization)
    (IntegralMixedFramedHeaderBits.routing P D)
    (IntegralMixedFramedNormalizationBits.routingAccess P a D H h.normalization) answer HR
  have EI := (IntegralMixedSquarefreeCoefficientNative.program P F).value_evaluator
    (IntegralMixedSquarefreeCoefficientNative.controls P a F I) answer HE
  have ES:=SpaceFunction.branch (fun q=>decide (IntegralMixedSquarefreeCoefficientNative.Selected P F q))
    (IntegralMixedSquarefreeCoefficientNative.selected_FP P a F I).flag_mem_FP EI (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q=>by
    change (if decide (IntegralMixedSquarefreeCoefficientNative.Selected P F q) then
      (IntegralMixedSquarefreeCoefficientNative.program P F).value answer q else [])=
      (if IntegralMixedSquarefreeCoefficientNative.Selected P F q then IntegralMixedSquarefreeCoefficientValue.value P F q else [])
    by_cases hs : IntegralMixedSquarefreeCoefficientNative.Selected P F q
    · simp only [hs,decide_true,ite_true]
      exact IntegralMixedSquarefreeCoefficientNative.value_at P F g answer q hs.1
        (IntegralMixedSquarefreeCoefficientNative.replies_of_matches P F g answer own q hs)
    · simp only [hs,decide_false,Bool.false_eq_true,ite_false])

end LeanCanny.Algebra.IntegralMixedFramedExceptionalProbeBits
