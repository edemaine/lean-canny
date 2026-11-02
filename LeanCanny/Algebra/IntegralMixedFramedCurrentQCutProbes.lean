/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateProbe
public import LeanCanny.Algebra.IntegralMixedFramedExceptionalProbes
public import LeanCanny.Algebra.IntegralMixedFramedLimitProbe
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
/-! # Full factor probes using the actual current-Q native arithmetic

These corollaries charge the proved seven-routine current-Q model. They do
not turn the changing prefix denominator into an original FP scalar leaf.
-/
@[expose] public section

namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateProbeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedCurrentQNativeBits.machine P a D H h).model
  have HE := IntegralMixedFramedCurrentQNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedCurrentQNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HV := IntegralMixedFramedCriticalBits.virtual_matches P a D H h.critical answer
    (IntegralMixedFramedCurrentQNativeBits.critical_matches P a D H h answer hm)
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  have EC := HE.precompose (IntegralMixedCoordinateCoefficientTasks.query P F)
    (IntegralMixedCoordinateCoefficientTasks.query_FP P a F I)
  have EI : SpaceFunction ((IntegralMixedCoordinateCoefficientNative.program P F).value answer) :=
    (SpaceFunction.branch (fun q=>decide (IntegralMixedValueCoefficientTasks.Labels P F q))
      (IntegralMixedValueCoefficientTasks.labels_FP P a F I).flag_mem_FP EC
      (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (by
        funext q
        simp only [SingleCall.Program.value,IntegralMixedCoordinateCoefficientNative.program,pairSnd_pair]
        rfl)
  have ES := SpaceFunction.branch (fun q=>decide (IntegralMixedCoordinateCoefficientNative.Selected P F q))
    (IntegralMixedCoordinateCoefficientNative.selected_FP P a F I).flag_mem_FP EI
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q=>by
    change (if decide (IntegralMixedCoordinateCoefficientNative.Selected P F q) then
      (IntegralMixedCoordinateCoefficientNative.program P F).value answer q else [])=
      (if IntegralMixedCoordinateCoefficientNative.Selected P F q then IntegralMixedCoordinateCoefficientValue.value P F q else [])
    by_cases hs : IntegralMixedCoordinateCoefficientNative.Selected P F q
    · simp only [hs,decide_true,ite_true]
      exact IntegralMixedCoordinateCoefficientNative.value_at P F (IntegralMixedFramedHistoryFamilyBits.geometry P D H)
        answer q hs.1 hs.2.2.2.1
        (IntegralMixedCoordinateCoefficientNative.replies_of_matches P F (IntegralMixedFramedHistoryFamilyBits.geometry P D H)
          answer HV q hs)
    · simp only [hs,decide_false,Bool.false_eq_true,ite_false])


end LeanCanny.Algebra.IntegralMixedFramedCoordinateProbeBits

namespace LeanCanny.Algebra.IntegralMixedFramedExceptionalProbeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

theorem currentQ_valueSelected_FP (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) :
    FPPred (ValueSelected P D H) :=
  (IntegralMixedValueCoefficientNative.selected_FP P a (family P D H)
    (IntegralMixedFramedNormalizationBits.input P a D H h.normalization)).and
      (IntegralMixedVirtualContextBits.context_FP P a)

theorem currentQ_value_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedCurrentQNativeBits.machine P a D H h).model
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  have HE := IntegralMixedFramedCurrentQNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedCurrentQNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HR:=IntegralMixedFramedCurrentQNativeBits.raw_matches P a D H h answer hm
  have own:=IntegralMixedRawDispatcherBits.valueFactor_matches P a F I
    (IntegralMixedFramedNormalizationBits.kind P a D H h.normalization)
    (IntegralMixedFramedNormalizationBits.degree P a D H h.normalization)
    (IntegralMixedFramedHeaderBits.routing P D)
    (IntegralMixedFramedNormalizationBits.routingAccess P a D H h.normalization) answer HR
  have EI := (IntegralMixedValueCoefficientNative.program P F).value_evaluator
    (IntegralMixedValueCoefficientNative.controls P a F I) answer HE
  have ES:=SpaceFunction.branch (fun q=>decide (ValueSelected P D H q)) (currentQ_valueSelected_FP P a D H h).flag_mem_FP
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


theorem currentQ_squarefree_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (squarefree P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedCurrentQNativeBits.machine P a D H h).model
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  have HE := IntegralMixedFramedCurrentQNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedCurrentQNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HR:=IntegralMixedFramedCurrentQNativeBits.raw_matches P a D H h answer hm
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

namespace LeanCanny.Algebra.IntegralMixedFramedLimitProbeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedCurrentQNativeBits.machine P a D H h).model
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  let R := IntegralMixedFramedHeaderBits.routing P D
  have RA := IntegralMixedFramedNormalizationBits.routingAccess P a D H h.normalization
  have HE := IntegralMixedFramedCurrentQNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedCurrentQNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HV := IntegralMixedFramedCriticalBits.virtual_matches P a D H h.critical answer
    (IntegralMixedFramedCurrentQNativeBits.critical_matches P a D H h answer hm)
  have HP := IntegralMixedFramedCurrentQNativeBits.producer_actual P a D H h answer hm
  have HC : BinaryFn (birth P) := BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)
  have HM := IntegralMixedLimitCoordinateRequests.modulusPredecessor_binary P a
  have HEX := IntegralMixedLimitCoordinateRequests.exponent_binary P a F I
  have EI : SpaceFunction ((IntegralMixedLimitCoordinateRequests.program P F R).value answer) :=
    TransformedRecursiveProduct.value_evaluator (fun q=>birth P q+1)
      (fun q=>BinaryNatCode.encode (IntegralMixedLimitCoordinateRequests.modulusPredecessor P q+1))
      (IntegralMixedLimitCoordinateRequests.task P F R)
      (PoweredPrefixProduct.transform (birth P) (IntegralMixedLimitCoordinateRequests.exponent P F)
        (IntegralMixedLimitCoordinateRequests.modulusPredecessor P))
      (HC.add (BinaryFn.const 1)) (HM.add (BinaryFn.const 1)).bits_mem_FP
      (IntegralMixedLimitCoordinateRequests.task_FP P a F I R RA)
      (PoweredPrefixProduct.transform_FP _ _ _ HC HEX HM)
      (fun q=>by simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]; omega) answer HE
  have ES := SpaceFunction.branch (fun q=>decide (IntegralMixedLimitCoordinateNative.Selected P F q))
    (IntegralMixedLimitCoordinateNative.selected_FP P a F I).flag_mem_FP EI (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q=>by
    change (if decide (IntegralMixedLimitCoordinateNative.Selected P F q) then
      (IntegralMixedLimitCoordinateRequests.program P F R).value answer q else [])=
      (if IntegralMixedLimitCoordinateNative.Selected P F q then IntegralMixedLimitCoordinateValue.value P F q else [])
    by_cases hs : IntegralMixedLimitCoordinateNative.Selected P F q
    · simp only [hs,decide_true,ite_true]
      exact IntegralMixedLimitCoordinateValue.value_at P F g R answer q hs.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2
        (IntegralMixedLimitCoordinateNative.replies_of_matches P F g R answer HV q hs
          (IntegralMixedFramedProducerActualBits.bank_replies P D H answer HP q hs.1))
    · simp only [hs,decide_false,Bool.false_eq_true,ite_false])


end LeanCanny.Algebra.IntegralMixedFramedLimitProbeBits
