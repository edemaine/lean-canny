/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
public import LeanCanny.Computation.NativePreparedSingleCallBranch
/-! # Native raw coordinate cuts restore their actual original payload before evaluation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPreparedCoordinateNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 4 ∧ isPhase .companion q ∧
    IntegralMixedVirtualContextBits.context P q ∧ IntegralMixedRawKindBits.tag F (IntegralMixedVirtualTaskBits.saved P q) = 2 ∧
    get P .coefficient q ≤ F.degree (IntegralMixedVirtualTaskBits.saved P q)

theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) :
    FPPred (Selected P F) := by
  have ht : BinaryFn (fun q => IntegralMixedRawKindBits.tag F (IntegralMixedVirtualTaskBits.saved P q)) :=
    h.tag.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 4)).and
      ((isPhase_FP .companion).and ((IntegralMixedVirtualContextBits.context_FP P a).and
        ((ht.eq (BinaryFn.const 2)).and
          ((get_binary P a .coefficient).le (hd.comp (IntegralMixedVirtualTaskBits.saved_FP P a)))))))

def replyWidth (P : Parameters) (q : List Bool) := (modulus P q).size

theorem replyWidth_unary (P : Parameters) (a : Access P) : UnaryFn (replyWidth P) :=
  (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) : Machine :=
  ofPreparedSingleCall (IntegralMixedCoordinateCoefficientNative.program P F)
    ((IntegralMixedCoordinateCoefficientNative.program P F).certificates (IntegralMixedCoordinateCoefficientNative.controls P a F h))
    (IntegralMixedRawKindBits.prepare P F) (IntegralMixedRawKindBits.prepare_FP P a F k)
    (fun q => decide (Selected P F q)) (selected_FP P a F k hd).flag_mem_FP
    (IntegralMixedNormalizationTopBits.rawCutValue P F) (replyWidth P) (replyWidth_unary P a)

theorem kernel_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) :
    IntegralMixedCoordinateCoefficientNative.Selected P F (IntegralMixedRawKindBits.prepare P F q) := by
  refine ⟨(IntegralMixedRawKindBits.prepare_valid P F q).mpr hs.1,
    IntegralMixedRawKindBits.prepare_routine P F q, IntegralMixedRawKindBits.prepare_phase P F q, ?_,
    (IntegralMixedRawKindBits.prepare_context P F g q).mpr hs.2.2.2.1⟩
  change get P .slot8 (IntegralMixedRawKindBits.prepare P F q) <
    IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
  rw [IntegralMixedRawKindBits.prepare_saved]
  simp only [IntegralMixedRawKindBits.prepare_get P F g q, reduceCtorEq, ite_false, ite_true]
  exact IntegralMixedRawKindBits.coordinate_choice_lt F _ hs.2.2.2.2.1

theorem raw_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (hs : Selected P F q) :
    IntegralMixedCoordinateCoefficientValue.value P F (IntegralMixedRawKindBits.prepare P F q) =
      IntegralMixedNormalizationTopBits.rawCutValue P F q := by
  have he := IntegralMixedCoordinateCoefficientSource.value_eq P F (IntegralMixedRawKindBits.prepare P F q)
    (IntegralMixedRawKindBits.prepare_coordinate_kind P F g q hs.2.2.2.2.1)
  have hd : get P .coefficient (IntegralMixedRawKindBits.prepare P F q) ≤
      F.degree (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)) := by
    rw [IntegralMixedRawKindBits.prepare_saved]
    simpa only [IntegralMixedRawKindBits.prepare_get P F g q, reduceCtorEq, ite_false] using hs.2.2.2.2.2
  rw [ite_eq_left hd] at he
  exact he.symm.trans ((IntegralMixedCoordinateCoefficientSource.value_rawCut P F _).trans
    (IntegralMixedRawKindBits.raw_value_prepare P F g q))

end LeanCanny.Algebra.IntegralMixedPreparedCoordinateNative
