/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueCoefficientTasks
/-! # The first-digit child is the literal natural value-coefficient entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueCoefficientValue
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedValueCoefficientTasks
open scoped Classical
attribute [local irreducible] IntegralMixedValueCoefficientSnapshot.first IntegralMixedValueCoefficientSnapshot.coefficient

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool := residueBits
  (IntegralMixedValueCoefficientSnapshot.coefficient F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) (get P .row q) (get P .col q) : ZMod (modulus P q))
theorem value_length (P : Parameters) (F : Family) (q : List Bool) [NeZero (modulus P q)] :
    (value P F q).length ≤ (modulus P q).size := residueBits_length_le _ _

theorem child_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hl : Labels P F q) :
    IntegralMixedValueFactorValue.value P F (query P F q) = value P F q := by
  rw [IntegralMixedValueCoefficientSnapshot.first_snapshot, query_saved]
  simp only [query_get P F g q hv hl, reduceCtorEq, ite_false, ite_true]
  have HM := congrArg (fun m : ℕ => residueBits
    (IntegralMixedValueCoefficientSnapshot.first F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) (packedRow P F q) (packedCol P F q) : ZMod m)) (query_modulus P F q)
  apply HM.trans
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (IntegralMixedValueCoefficientSnapshot.first_coefficient F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) ⟨get P .row q, hl.1⟩ ⟨get P .col q, hl.2.1⟩
      ⟨get P .coefficient q, hl.2.2⟩)

private theorem zero_outside {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : ℕ)
    (h : ¬(r < n ∧ t < n)) : IntegralCriticalTotalSnapshotBits.integerEntry M r t = 0 := by
  by_cases hr : r < n
  · have ht : ¬t < n := fun ht => h ⟨hr, ht⟩
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_left hr, dite_eq_right ht]
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_right hr]

theorem value_outside (P : Parameters) (F : Family) (q : List Bool) (hl : ¬Labels P F q) : value P F q = [] := by
  have HZ : IntegralMixedValueCoefficientSnapshot.coefficient F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) (get P .row q) (get P .col q) = 0 := by
    by_cases hb : get P .row q < oldRank P F q ∧ get P .col q < oldRank P F q
    · exact IntegralMixedValueCoefficientSnapshot.coefficient_zero F _ _ _ _ _ _ (by
        have H : ¬get P .coefficient q < scalar P F q := fun h => hl ⟨hb.1, hb.2, h⟩
        exact Nat.le_of_not_gt H)
    · unfold IntegralMixedValueCoefficientSnapshot.coefficient
      exact zero_outside _ _ _ hb
  exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) HZ).trans
    (by simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])

end LeanCanny.Algebra.IntegralMixedValueCoefficientValue
