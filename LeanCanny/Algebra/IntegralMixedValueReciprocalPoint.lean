/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalChildren

/-! # Actual reciprocal matrix entries from the same-parent homogeneous reply -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalPoint
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask IntegralCoordinateBasis
open IntegralMixedCutSource IntegralMixedValueReciprocalTasks IntegralMixedValueReciprocalRequest
open scoped Classical

theorem value_zero (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (u v : Fin (count ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q)))
    (a c : Fin (2 ^ (IntegralMixedVirtualTaskBits.family P F).width q))
    (hs : get P .slot8 q = 0) (hk : get P .target q = k.val)
    (hr : get P .row q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a)).val)
    (ht : get P .col q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)).val)
    (he : RepliesAt P F reply q) :
    (program P F).value reply q = residueBits
      (IntegralMixedValueReciprocalMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q 0 k
        (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a))
        (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)) :
          ZMod (modulus P q)) := by
  have HP := IntegralMixedValueReciprocalChildren.packet_eq P F q 0 k u v a c hs hk hr ht
  rw [packet_value, HP]
  unfold IntegralMixedValueReciprocalMatrix.entry
  apply IntegralMixedValueSystemActual.value_zero (IntegralMixedVirtualTaskBits.family P F)
    (IntegralMixedVirtualTaskBits.indices P F) (fun _ => reply (query P F q)) q k u v a c
  intro HD
  have HQ : request P F q := by
    change IntegralReciprocalEntryRequest.request (parameters P F) (IntegralMixedValueHomogeneousQueries.packet P q)
    rw [HP]
    exact (IntegralMixedValueSystemSemantics.request_zero (IntegralMixedVirtualTaskBits.family P F)
      (IntegralMixedVirtualTaskBits.indices P F) q k u v a c).mpr HD
  change reply (query P F q) = _
  have HC := IntegralMixedValueReciprocalChildren.homogeneous_reply P F q 0 k u v a c hs hk hr ht
  rw [IntegralMixedValueHomogeneousMatrix.entry_zero] at HC
  exact (he HQ).trans HC

theorem value_succ (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (j : Fin (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q))
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (u v : Fin (count ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q)))
    (a c : Fin (2 ^ (IntegralMixedVirtualTaskBits.family P F).width q))
    (hs : get P .slot8 q = j.succ.val) (hk : get P .target q = k.val)
    (hr : get P .row q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a)).val)
    (ht : get P .col q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)).val)
    (he : RepliesAt P F reply q) :
    (program P F).value reply q = residueBits
      (IntegralMixedValueReciprocalMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q j.succ k
        (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a))
        (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)) :
          ZMod (modulus P q)) := by
  have HP := IntegralMixedValueReciprocalChildren.packet_eq P F q j.succ k u v a c hs hk hr ht
  rw [packet_value, HP]
  unfold IntegralMixedValueReciprocalMatrix.entry
  apply IntegralMixedValueSystemActual.value_succ (IntegralMixedVirtualTaskBits.family P F)
    (IntegralMixedVirtualTaskBits.indices P F) (fun _ => reply (query P F q)) q j k u v a c
  intro HD
  have HQ : request P F q := by
    change IntegralReciprocalEntryRequest.request (parameters P F) (IntegralMixedValueHomogeneousQueries.packet P q)
    rw [HP]
    exact (IntegralMixedValueSystemSemantics.request_succ (IntegralMixedVirtualTaskBits.family P F)
      (IntegralMixedVirtualTaskBits.indices P F) q j k u v a c).mpr HD
  change reply (query P F q) = _
  have HC := IntegralMixedValueReciprocalChildren.homogeneous_reply P F q j.succ k u v a c hs hk hr ht
  rw [IntegralMixedValueHomogeneousMatrix.entry_succ] at HC
  rw [IntegralMixedValueHomogeneousSource.coordinate_entry]
  exact (he HQ).trans HC

end LeanCanny.Algebra.IntegralMixedValueReciprocalPoint
