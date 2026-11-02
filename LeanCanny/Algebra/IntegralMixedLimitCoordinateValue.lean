/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRequests
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateSnapshot
public import LeanCanny.Algebra.PoweredPrefixProductModulus
/-! # Actual limit coefficients from earlier leading replies and one critical reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateValue
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedOldBankCofactorBits (Routing)
open IntegralMixedValueCoefficientTasks (Labels)
open scoped Classical BigOperators
attribute [local irreducible] IntegralMixedCoordinateCoefficientSnapshot.coefficient IntegralMixedLimitCoordinateSnapshot.coefficient

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool := residueBits
  (IntegralMixedLimitCoordinateSnapshot.coefficient F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) (get P .row q) (get P .col q) : ZMod (modulus P q))

noncomputable def oldCoefficient (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  IntegralMixedCoordinateCoefficientSnapshot.coefficient F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (get P .coefficient q) (get P .slot8 q-get P .coefficient q) (get P .row q) (get P .col q)

noncomputable def bankScalar (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) : ℤ :=
  IntegralMixedBankCofactor.scale (IntegralMixedVirtualTaskBits.family P F) q i

structure RepliesAt (P : Parameters) (F : Family) (R : Routing) (answer : List Bool → List Bool) (q : List Bool) : Prop where
  bank : IntegralMixedOldBankCofactorBits.RepliesAt P F R answer q
  critical : answer (IntegralMixedLimitCoordinateTasks.critical P F q) =
    (IntegralMixedVirtualTaskBits.source P F).value (IntegralMixedLimitCoordinateTasks.critical P F q)

theorem choiceBound_prepare (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedCoordinateCoefficientTasks.choiceBound P F (IntegralMixedLimitCoordinateTasks.prepare P q) =
      IntegralMixedCoordinateCoefficientTasks.choiceBound P F q := by
  change IntegralMixedCoordinateTrailing.ChoiceBound
      (F.spatial (IntegralMixedVirtualTaskBits.saved P (IntegralMixedLimitCoordinateTasks.prepare P q)))
      (F.rule (IntegralMixedVirtualTaskBits.saved P (IntegralMixedLimitCoordinateTasks.prepare P q))) = _
  rw [IntegralMixedLimitCoordinateTasks.prepare_saved]
  rfl

theorem exponent_eq (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedLimitCoordinateRequests.exponent P F q =
      IntegralMixedLimitCoordinateSnapshot.degree F (IntegralMixedVirtualTaskBits.saved P q)-get P .coefficient q := by
  change (IntegralMixedLimitCoordinateSnapshot.degree F (IntegralMixedVirtualTaskBits.saved P q)+1)-1-get P .coefficient q = _
  omega

theorem critical_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hc : get P .slot8 q < IntegralMixedCoordinateCoefficientTasks.choiceBound P F q)
    (hk : get P .coefficient q ≤ get P .slot8 q) (hl : Labels P F (IntegralMixedLimitCoordinateTasks.prepare P q)) :
    (IntegralMixedVirtualTaskBits.source P F).value (IntegralMixedLimitCoordinateTasks.critical P F q) =
      residueBits (oldCoefficient P F q : ZMod (modulus P q)) := by
  have HB : get P .slot8 (IntegralMixedLimitCoordinateTasks.prepare P q) <
      IntegralMixedCoordinateCoefficientTasks.choiceBound P F (IntegralMixedLimitCoordinateTasks.prepare P q) := by
    rw [IntegralMixedLimitCoordinateTasks.prepare_get, choiceBound_prepare]
    exact hk.trans_lt hc
  have H := IntegralMixedCoordinateCoefficientValue.child_value P F g (IntegralMixedLimitCoordinateTasks.prepare P q)
    ((IntegralMixedLimitCoordinateTasks.prepare_valid P q).mpr hv) hl HB
  change (IntegralMixedVirtualTaskBits.source P F).value (IntegralMixedLimitCoordinateTasks.critical P F q) = _ at H
  apply H.trans
  unfold IntegralMixedCoordinateCoefficientValue.value
  rw [IntegralMixedLimitCoordinateTasks.prepare_saved, IntegralMixedLimitCoordinateTasks.prepare_modulus]
  simp only [IntegralMixedLimitCoordinateTasks.prepare_get, reduceCtorEq, ite_false, ite_true]
  rfl

theorem bank_product (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    (∏ i ∈ Finset.range (birth P q), bankScalar P F q i) =
      IntegralMixedLimitCoordinateSnapshot.denominator F (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [← IntegralMixedOldBankCofactorBits.count_eq P F g q]
  exact IntegralMixedBankCofactor.denominator_eq (IntegralMixedVirtualTaskBits.family P F)
    (modulus P) (modulus_ne_zero P) (fun _ => 0) q

theorem leading_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (answer : List Bool → List Bool) (q : List Bool)
    (he : IntegralMixedOldBankCofactorBits.RepliesAt P F R answer q) (i : ℕ) (hi : i<birth P q) :
    answer (IntegralMixedLimitCoordinateRequests.task P F R (pair q (BinaryNatCode.encode i))) =
      residueBits (bankScalar P F q i : ZMod (modulus P q)) := by
  rw [IntegralMixedLimitCoordinateRequests.task_leading P F g R q i hi]
  have HI : i<IntegralMixedOldBankCofactorBits.count P F q :=
    hi.trans_eq (IntegralMixedOldBankCofactorBits.count_eq P F g q).symm
  unfold bankScalar IntegralMixedBankCofactor.scale
  have HI' : i<(IntegralMixedVirtualTaskBits.family P F).birth q := HI
  rw [dite_eq_left HI']
  exact he ⟨i, HI⟩

attribute [local irreducible] bankScalar oldCoefficient value IntegralMixedLimitCoordinateSnapshot.denominator

theorem bank_product_cast (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    (∏ i ∈ Finset.range (birth P q), (bankScalar P F q i : ZMod (modulus P q))) =
      (IntegralMixedLimitCoordinateSnapshot.denominator F (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  calc
    _ = ((∏ i ∈ Finset.range (birth P q), bankScalar P F q i : ℤ) : ZMod (modulus P q)) :=
      (Int.cast_prod (R := ZMod (modulus P q)) (bankScalar P F q) (Finset.range (birth P q))).symm
    _ = _ := congrArg (fun z : ℤ => (z : ZMod (modulus P q))) (bank_product P F g q)

theorem value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (answer : List Bool → List Bool) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hc : get P .slot8 q < IntegralMixedCoordinateCoefficientTasks.choiceBound P F q)
    (hk : get P .coefficient q ≤ get P .slot8 q) (hl : Labels P F (IntegralMixedLimitCoordinateTasks.prepare P q))
    (he : RepliesAt P F R answer q) :
    (IntegralMixedLimitCoordinateRequests.program P F R).value answer q = value P F q := by
  have HL : answer (IntegralMixedLimitCoordinateRequests.task P F R (pair q (BinaryNatCode.encode (birth P q)))) =
      residueBits (oldCoefficient P F q : ZMod (modulus P q)) := by
    rw [IntegralMixedLimitCoordinateRequests.task_last]
    exact he.critical.trans (critical_value P F g q hv hc hk hl)
  have H := PoweredPrefixProductModulus.value (birth P) (IntegralMixedLimitCoordinateRequests.exponent P F)
    (IntegralMixedLimitCoordinateRequests.modulusPredecessor P) (IntegralMixedLimitCoordinateRequests.task P F R)
    answer (modulus P) (funext (IntegralMixedLimitCoordinateRequests.modulusPredecessor_value P)) q
    (fun i => (bankScalar P F q i : ZMod (modulus P q))) (oldCoefficient P F q : ZMod (modulus P q))
    (leading_reply P F g R answer q he.bank) HL
  rw [bank_product_cast P F g q, exponent_eq] at H
  apply H.trans
  unfold value
  rw [IntegralMixedLimitCoordinateSnapshot.coefficient_eq F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) (get P .row q) (get P .col q) hc, ite_eq_left hk]
  apply congrArg (fun z : ZMod (modulus P q) => residueBits z)
  simp only [Int.cast_mul, Int.cast_pow]
  unfold oldCoefficient
  rfl

end LeanCanny.Algebra.IntegralMixedLimitCoordinateValue
