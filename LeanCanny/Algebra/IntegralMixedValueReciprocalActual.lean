/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalPoint

/-! # Total actual second-digit matrix-entry correctness -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalActual
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask IntegralCoordinateBasis
open IntegralMixedCutSource IntegralMixedValueReciprocalTasks IntegralMixedValueReciprocalRequest
open scoped Classical

theorem value_finite (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (s : Fin (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1))
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (r t : Fin (IntegralMixedValueReciprocalMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q))
    (hs : get P .slot8 q = s.val) (hk : get P .target q = k.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val) (he : RepliesAt P F reply q) :
    (program P F).value reply q = residueBits
      (IntegralMixedValueReciprocalMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q s k r t : ZMod (modulus P q)) := by
  obtain ⟨⟨u, a⟩, rfl⟩ := (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
    ((IntegralMixedVirtualTaskBits.family P F).width q)).surjective r
  obtain ⟨⟨v, c⟩, rfl⟩ := (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
    ((IntegralMixedVirtualTaskBits.family P F).width q)).surjective t
  cases s using Fin.cases with
  | zero => exact IntegralMixedValueReciprocalPoint.value_zero P F reply q k u v a c hs hk hr ht he
  | succ j => exact IntegralMixedValueReciprocalPoint.value_succ P F reply q j k u v a c hs hk hr ht he

theorem value_at (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : RepliesAt P F reply q) : (program P F).value reply q = IntegralMixedValueReciprocalMatrix.value P F q := by
  by_cases HL : IntegralMixedValueReciprocalMatrix.Labels (IntegralMixedVirtualTaskBits.family P F) q
      (get P .slot8 q) (get P .target q) (get P .row q) (get P .col q)
  · let s : Fin (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1) := ⟨get P .slot8 q, HL.1⟩
    let k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
        (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)) := ⟨get P .target q, HL.2.1⟩
    let r : Fin (IntegralMixedValueReciprocalMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q) := ⟨get P .row q, HL.2.2.1⟩
    let t : Fin (IntegralMixedValueReciprocalMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q) := ⟨get P .col q, HL.2.2.2⟩
    change _ = residueBits (IntegralMixedValueReciprocalMatrix.totalEntry
      (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F) q
        s.val k.val r.val t.val : ZMod (modulus P q))
    rw [IntegralMixedValueReciprocalMatrix.total_finite]
    exact value_finite P F reply q s k r t rfl rfl rfl rfl he
  · have HV : ¬IntegralReciprocalEntryRequest.valid (parameters P F) (IntegralMixedValueHomogeneousQueries.packet P q) := by
      intro H
      exact HL ((IntegralMixedValueReciprocalMatrix.labels_iff (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q _ _ _ _).mpr H)
    have HN : ¬request P F q := fun H => HV H.1
    have HC : ¬IntegralReciprocalEntryRequest.chart (parameters P F) (IntegralMixedValueHomogeneousQueries.packet P q) :=
      fun H => HV H.1
    rw [value_eq, ite_eq_right HN, immediate, IntegralReciprocalEntryRequest.immediate, ite_eq_right HC]
    unfold IntegralMixedValueReciprocalMatrix.value
    rw [IntegralMixedValueReciprocalMatrix.total_invalid _ _ _ _ _ _ _ HL]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.IntegralMixedValueReciprocalActual
