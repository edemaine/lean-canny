/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayChildren

/-! # An actual rectangular entry from its one guarded shifted reply -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayPoint
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedValueMacaulayTasks IntegralMixedValueMacaulayRequest
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

theorem value_finite (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool)
    (a : Fin (IntegralMixedValueMacaulayMatrix.rows (IntegralMixedVirtualTaskBits.family P F) q))
    (b : Fin (IntegralMixedValueMacaulayMatrix.columns (IntegralMixedVirtualTaskBits.family P F) q))
    (r t : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q))
    (ha : get P .slot8 q = a.val) (hb : get P .slot9 q = b.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (he : RepliesAt P F reply q) :
    (program P F).value reply q = residueBits
      (IntegralMixedValueMacaulayMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q a b r t : ZMod (modulus P q)) := by
  have HV : BasisValid P F q := by
    unfold BasisValid
    rw [hr, ht]
    exact ⟨r.isLt, t.isLt⟩
  have HP : packet P q = MacaulayFullBoxBits.entryPacket q a.val b.val r.val t.val := by
    simp only [packet, ha, hb, hr, ht]
  let row := (IntegralMixedValueGramEntry.rowEquiv ((layout P F).arity q) ((layout P F).width q)).symm a
  have HN : MacaulayFullBoxBits.rowNumber _ _ row = a.val :=
    IntegralMixedValueGramFromRows.rowNumber_symm _ _ a
  rw [packet_value P F reply q HV, HP, ← HN]
  have H := MacaulayIntegralLocalCorrect.actual_value
    (IntegralMixedValueDoubleNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q))
    (layout P F) (fun _ => reply (query P F q)) q
    (IntegralMixedValueDoubleSystem.mappedSystem (IntegralMixedVirtualTaskBits.family P F) q
      ((IntegralMixedVirtualTaskBits.indices P F).coordinate q))
    (by rw [IntegralMixedValueMacaulayEntry.degrees_eq]; rfl)
    (modulus P) (Nat.pos_of_ne_zero (modulus_ne_zero P q)) r t row b ?_
  · rw [IntegralMixedValueMacaulayEntry.degrees_eq] at H
    exact H
  · intro HQ
    have HQ' : MacaulayIntegralEntryRequest.request (layout P F) (packet P q) := by
      rw [HP, ← HN]
      exact HQ
    exact (he ⟨HV, HQ'⟩).trans
      (by
        have HC := IntegralMixedValueMacaulayChildren.coefficient_reply P F g q r t hr ht HQ'
        rw [queryPacket, HP, ← HN] at HC
        exact HC)

end LeanCanny.Algebra.IntegralMixedValueMacaulayPoint
