/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayPoint

/-! # Total native rectangular-entry correctness, including invalid labels -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayActual
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedValueMacaulayTasks IntegralMixedValueMacaulayRequest
open scoped Classical

theorem invalid_rectangle (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (hv : ¬MacaulayIntegralEntryRequest.valid (layout P F) (packet P q)) :
    (program P F).value reply q = [] := by
  have HN : ¬request P F q := fun H => hv H.2.1
  rw [value_eq, ite_eq_right HN]
  unfold immediate
  split
  · unfold MacaulayIntegralEntryRequest.immediate
    exact ite_eq_right (fun H => hv H.1)
  · rfl

theorem value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F reply q) :
    (program P F).value reply q = IntegralMixedValueMacaulayMatrix.value P F q := by
  by_cases HL : IntegralMixedValueMacaulayMatrix.Labels (IntegralMixedVirtualTaskBits.family P F) q
      (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q)
  · let a : Fin (IntegralMixedValueMacaulayMatrix.rows (IntegralMixedVirtualTaskBits.family P F) q) := ⟨get P .slot8 q, HL.1⟩
    let b : Fin (IntegralMixedValueMacaulayMatrix.columns (IntegralMixedVirtualTaskBits.family P F) q) := ⟨get P .slot9 q, HL.2.1⟩
    let r : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q) := ⟨get P .row q, HL.2.2.1⟩
    let t : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q) := ⟨get P .col q, HL.2.2.2⟩
    change _ = residueBits (IntegralMixedValueMacaulayMatrix.totalEntry
      (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F) q
        a.val b.val r.val t.val : ZMod (modulus P q))
    rw [IntegralMixedValueMacaulayMatrix.total_finite]
    exact IntegralMixedValueMacaulayPoint.value_finite P F g reply q a b r t rfl rfl rfl rfl he
  · have HZ : (program P F).value reply q = [] := by
      by_cases HB : BasisValid P F q
      · apply invalid_rectangle
        intro HV
        have HR := (IntegralMixedValueMacaulayMatrix.valid_packet_iff (layout P F) q
          (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q)).mp HV
        exact HL ⟨HR.1, HR.2, HB.1, HB.2⟩
      · exact basis_invalid P F reply q HB
    rw [HZ]
    unfold IntegralMixedValueMacaulayMatrix.value
    rw [IntegralMixedValueMacaulayMatrix.total_invalid _ _ _ _ _ _ _ HL]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.IntegralMixedValueMacaulayActual
