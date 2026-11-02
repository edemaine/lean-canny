/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientClosure
/-! # Untruncated coordinate-factor probes from the actual complete native model

Unlike normalization's rawCutValue, this probe retains coefficients above
the recorded scalar degree. Its only charged child is the existing virtual
critical polynomial. Task validity is explicit, including its honest bounded
modulus; the whole-history space certificate is derived from native controls
and their verified bounds, not supplied as a coefficient evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateProbeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if IntegralMixedCoordinateCoefficientNative.Selected P (family P D H) q then
    IntegralMixedCoordinateCoefficientValue.value P (family P D H) q else []

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let F := family P D H
  let answer := (IntegralMixedFramedNativeBits.machine P a D H h).model
  have HE := IntegralMixedFramedNativeBits.model_space P a D H h hb
  have hm : IntegralMixedFramedNativeBits.Matches P a D H h answer := fun _ _=>rfl
  have HV := IntegralMixedFramedCriticalBits.virtual_matches P a D H h.critical answer
    (IntegralMixedFramedNativeBits.critical_matches P a D H h answer hm)
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

theorem selected_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hs : IntegralMixedCoordinateCoefficientNative.Selected P (family P D H) q) :
    value P D H q=IntegralMixedCoordinateCoefficientValue.value P (family P D H) q := ite_eq_left hs

end LeanCanny.Algebra.IntegralMixedFramedCoordinateProbeBits
