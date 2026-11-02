/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateClosure
/-! # Total natural-index zero guards for the native limit coefficient branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedValueCoefficientTasks (Labels oldRank scalar)
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedLimitCoordinateValue
open scoped Classical
attribute [local irreducible] IntegralMixedLimitCoordinateValue.value
attribute [local irreducible] IntegralMixedLimitCoordinateSnapshot.coefficient IntegralMixedCoordinateCoefficientSnapshot.coefficient

theorem labels_prepare_iff (P : Parameters) (F : Family) (q : List Bool) :
    Labels P F (IntegralMixedLimitCoordinateTasks.prepare P q) ↔
      get P .row q<oldRank P F q ∧ get P .col q<oldRank P F q ∧
        get P .slot8 q-get P .coefficient q<scalar P F q := by
  unfold Labels oldRank scalar
  simp only [IntegralMixedLimitCoordinateTasks.prepare_saved, IntegralMixedLimitCoordinateTasks.prepare_get,
    reduceCtorEq, ite_false, ite_true]

theorem value_outside (P : Parameters) (F : Family) (q : List Bool)
    (hc : get P .slot8 q<IntegralMixedCoordinateCoefficientTasks.choiceBound P F q)
    (hk : get P .coefficient q≤get P .slot8 q) (hl : ¬Labels P F (IntegralMixedLimitCoordinateTasks.prepare P q)) :
    value P F q=[] := by
  have HZ : IntegralMixedLimitCoordinateSnapshot.coefficient F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) (get P .row q) (get P .col q)=0 := by
    by_cases hr : get P .row q<oldRank P F q
    · by_cases ht : get P .col q<oldRank P F q
      · have HB : scalar P F q≤get P .slot8 q-get P .coefficient q := by
          exact Nat.le_of_not_gt (fun hb => hl ((labels_prepare_iff P F q).mpr ⟨hr, ht, hb⟩))
        rw [IntegralMixedLimitCoordinateSnapshot.coefficient_eq F (IntegralMixedVirtualTaskBits.saved P q)
          (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) (get P .row q) (get P .col q) hc, ite_eq_left hk,
          IntegralMixedCoordinateCoefficientSnapshot.coefficient_zero F _ _ _ _ _ _ HB, mul_zero]
      · exact IntegralMixedLimitCoordinateSnapshot.coefficient_invalid_col F _ _ _ _ _ _ (Nat.le_of_not_gt ht)
    · exact IntegralMixedLimitCoordinateSnapshot.coefficient_invalid_row F _ _ _ _ _ _ (Nat.le_of_not_gt hr)
  unfold IntegralMixedLimitCoordinateValue.value
  rw [HZ]
  simp [residueBits]

theorem value_above (P : Parameters) (F : Family) (q : List Bool)
    (hc : get P .slot8 q<IntegralMixedCoordinateCoefficientTasks.choiceBound P F q)
    (hk : ¬get P .coefficient q≤get P .slot8 q) : value P F q=[] := by
  unfold IntegralMixedLimitCoordinateValue.value
  rw [IntegralMixedLimitCoordinateSnapshot.coefficient_zero F _ _ _ _ _ _ hc (by omega)]
  simp [residueBits]

noncomputable def branch (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (R : Routing) (hr : RoutingAccess R) :=
  (machine P a F h R hr).choose zero

theorem branch_value (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (R : Routing) (hr : RoutingAccess R) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hR : IntegralMixedRoutineTaskBits.routine P q=4) (hp : isPhase .companion q)
    (hx : IntegralMixedVirtualContextBits.context P q)
    (hc : get P .slot8 q<IntegralMixedCoordinateCoefficientTasks.choiceBound P F q) :
    (branch P a F h R hr).model q=value P F q := by
  change (if decide (Selected P F q) then value P F q else [])=value P F q
  by_cases hs : Selected P F q
  · rw [ite_eq_left (decide_eq_true hs)]
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hs)]
    by_cases hk : get P .coefficient q≤get P .slot8 q
    · have hl : ¬Labels P F (IntegralMixedLimitCoordinateTasks.prepare P q) := fun hl => hs ⟨hv,hR,hp,hx,hc,hk,hl⟩
      exact (value_outside P F q hc hk hl).symm
    · exact (value_above P F q hc hk).symm

theorem branch_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (bank : ∀ q, Selected P F q → IntegralMixedOldBankCofactorBits.RepliesAt P F R answer q) :
    Correct (branch P a F h R hr) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  choose_correct _ _ answer _ (correct_of_matches P a F h g R hr answer own bank) (zero_correct answer _)

end LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
