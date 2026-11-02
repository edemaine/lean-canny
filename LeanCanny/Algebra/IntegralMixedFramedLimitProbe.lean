/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
public import LeanCanny.Algebra.TransformedRecursiveProductSpace
/-! # Full limit-factor coefficient probes from current native replies

The powered product charges every actual older producing leading and the
current virtual critical coefficient. It does not use the recorded scalar
degree truncation, a factor oracle, modular division, or a fresh root.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedLimitProbeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if IntegralMixedLimitCoordinateNative.Selected P (family P D H) q then
    IntegralMixedLimitCoordinateValue.value P (family P D H) q else []

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedNativeBits.machine P a D H h).model
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  let I := IntegralMixedFramedNormalizationBits.input P a D H h.normalization
  let R := IntegralMixedFramedHeaderBits.routing P D
  have RA := IntegralMixedFramedNormalizationBits.routingAccess P a D H h.normalization
  have HE := IntegralMixedFramedNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HV := IntegralMixedFramedCriticalBits.virtual_matches P a D H h.critical answer
    (IntegralMixedFramedNativeBits.critical_matches P a D H h answer hm)
  have HP := IntegralMixedFramedNativeBits.producer_actual P a D H h answer hm
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
