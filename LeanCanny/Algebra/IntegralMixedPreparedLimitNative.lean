/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindLimitSelection
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateOutside
public import LeanCanny.Computation.NativePreparedBranch
/-! # Prepared limit cuts retain their literal truncated raw-source model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPreparedLimitNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical
attribute [local irreducible] IntegralMixedLimitCoordinate.factor IntegralMixedLimitCoordinateValue.value

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q=4 ∧ isPhase .companion q ∧
    IntegralMixedVirtualContextBits.context P q ∧ IntegralMixedRawKindBits.tag F (IntegralMixedVirtualTaskBits.saved P q)=5 ∧
    get P .coefficient q≤F.degree (IntegralMixedVirtualTaskBits.saved P q)

theorem selected_FP (P : Parameters) (a : Access P) (F : Family)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) : FPPred (Selected P F) := by
  have HT : BinaryFn (fun q => IntegralMixedRawKindBits.tag F (IntegralMixedVirtualTaskBits.saved P q)) :=
    k.tag.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 4)).and
      ((isPhase_FP .companion).and ((IntegralMixedVirtualContextBits.context_FP P a).and
        ((HT.eq (BinaryFn.const 5)).and
          ((get_binary P a .coefficient).le (hd.comp (IntegralMixedVirtualTaskBits.saved_FP P a)))))))

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (R : Routing) (hr : RoutingAccess R) : Machine :=
  NativePreparedBranch.machine (IntegralMixedLimitCoordinateNative.branch P a F h R hr)
    (IntegralMixedRawKindBits.prepare P F) (IntegralMixedRawKindBits.prepare_FP P a F k)
    (fun q => decide (Selected P F q)) (selected_FP P a F k hd).flag_mem_FP
    (IntegralMixedNormalizationTopBits.rawCutValue P F)

theorem kernel_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (R : Routing) (hr : RoutingAccess R) (q : List Bool) :
    (IntegralMixedLimitCoordinateNative.branch P a F h R hr).selected (IntegralMixedRawKindBits.prepare P F q)=true := by
  change (_ || true)=true
  exact Bool.or_true _

private theorem value_eq (P : Parameters) (F : Family) (q : List Bool)
    (hkind : F.kind (IntegralMixedVirtualTaskBits.saved P q) =
      IntegralMixedRawKindBits.limitKind F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q))
    (hd : get P .coefficient q≤F.degree (IntegralMixedVirtualTaskBits.saved P q)) :
    IntegralMixedLimitCoordinateValue.value P F q=IntegralMixedNormalizationTopBits.rawCutValue P F q := by
  unfold IntegralMixedLimitCoordinateValue.value IntegralMixedNormalizationTopBits.rawCutValue
  rw [IntegralMixedCutSource.source_coefficient F _ _, ite_eq_left hd]
  unfold IntegralMixedCutMatrix.coefficientMatrix
  rw [hkind]
  rfl

theorem raw_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) :
    IntegralMixedLimitCoordinateValue.value P F (IntegralMixedRawKindBits.prepare P F q) =
      IntegralMixedNormalizationTopBits.rawCutValue P F q := by
  have HD : get P .coefficient (IntegralMixedRawKindBits.prepare P F q)≤
      F.degree (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)) := by
    rw [IntegralMixedRawKindBits.prepare_saved]
    simpa only [IntegralMixedRawKindBits.prepare_get P F g q, reduceCtorEq, ite_false] using hs.2.2.2.2.2
  exact (value_eq P F _ (IntegralMixedRawKindBits.prepare_limit_kind P F g q hs.2.2.2.2.1) HD).trans
    (IntegralMixedRawKindBits.raw_value_prepare P F g q)

theorem kernel_value (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R)
    (q : List Bool) (hs : Selected P F q) :
    (IntegralMixedLimitCoordinateNative.branch P a F h R hr).model (IntegralMixedRawKindBits.prepare P F q)=
      IntegralMixedNormalizationTopBits.rawCutValue P F q := by
  have HC : get P .slot8 (IntegralMixedRawKindBits.prepare P F q) <
      IntegralMixedCoordinateCoefficientTasks.choiceBound P F (IntegralMixedRawKindBits.prepare P F q) := by
    change get P .slot8 (IntegralMixedRawKindBits.prepare P F q) <
      IntegralMixedCoordinateTrailing.ChoiceBound
        (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
        (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedRawKindBits.prepare P F q)))
    rw [IntegralMixedRawKindBits.prepare_saved]
    simp only [IntegralMixedRawKindBits.prepare_get P F g q, reduceCtorEq, ite_false, ite_true]
    exact IntegralMixedRawKindBits.limit_choice_lt F _ hs.2.2.2.2.1
  have H := IntegralMixedLimitCoordinateNative.branch_value P a F h R hr (IntegralMixedRawKindBits.prepare P F q)
    ((IntegralMixedRawKindBits.prepare_valid P F q).mpr hs.1) (IntegralMixedRawKindBits.prepare_routine P F q)
    (IntegralMixedRawKindBits.prepare_phase P F q) ((IntegralMixedRawKindBits.prepare_context P F g q).mpr hs.2.2.2.1) HC
  exact H.trans (raw_value P F g q hs)

end LeanCanny.Algebra.IntegralMixedPreparedLimitNative
