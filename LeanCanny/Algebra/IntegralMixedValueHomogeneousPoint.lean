/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousChildren

/-! # Actual homogeneous matrix entries from current smaller-task replies -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousPoint
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueHomogeneousQueries
open scoped Classical

noncomputable def currentValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if get P .slot8 q = 0 then IntegralMixedValueRestoredSource.value P F (query P F q)
  else (IntegralMixedVirtualTaskBits.source P F).value (query P F q)

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  IntegralMixedValueHomogeneousRequest.request P F q → reply (query P F q) = currentValue P F q

theorem value_zero (P : Parameters) (F : Family) (g : RootGeometry P F) (reply : List Bool → List Bool)
    (q : List Bool) (k : Fin (count ((parameters P F).free q + 1) ((parameters P F).width q)))
    (r t : Fin ((parameters P F).rank q))
    (hs : get P .slot8 q = 0) (hk : get P .target q = k.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (he : RepliesAt P F reply q) :
    (IntegralMixedValueHomogeneousRequest.program P F).value reply q =
      residueBits (IntegralMixedValueHomogeneousMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q 0 k r t : ZMod (modulus P q)) := by
  have HP := IntegralMixedValueHomogeneousChildren.packet_eq P q 0 k.val r.val t.val hs hk hr ht
  rw [IntegralMixedValueHomogeneousRequest.packet_value, HP, IntegralMixedValueHomogeneousMatrix.entry_zero]
  apply IntegralMixedValueHomogeneousSource.value_zero
    (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)
    (fun _ => reply (query P F q)) q k r t
  intro HW
  have HQ : IntegralMixedValueHomogeneousRequest.request P F q := by
    change HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)
    rw [HP]
    exact (HomogeneousSystemCoefficientSemantics.request_zero_packet (parameters P F) q k r t).mpr HW
  change reply (query P F q) = _
  rw [he HQ]
  unfold currentValue
  rw [ite_eq_left hs, query, ite_eq_left hs]
  exact IntegralMixedValueHomogeneousChildren.original_reply P F g q k r t hs hk hr ht HQ

theorem value_succ (P : Parameters) (F : Family) (g : RootGeometry P F) (reply : List Bool → List Bool)
    (q : List Bool) (j : Fin ((parameters P F).free q))
    (k : Fin (count ((parameters P F).free q + 1) ((parameters P F).width q)))
    (r t : Fin ((parameters P F).rank q))
    (hs : get P .slot8 q = j.succ.val) (hk : get P .target q = k.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (he : RepliesAt P F reply q) :
    (IntegralMixedValueHomogeneousRequest.program P F).value reply q =
      residueBits (IntegralMixedValueHomogeneousMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q j.succ k r t : ZMod (modulus P q)) := by
  have HP := IntegralMixedValueHomogeneousChildren.packet_eq P q j.succ.val k.val r.val t.val hs hk hr ht
  rw [IntegralMixedValueHomogeneousRequest.packet_value, HP, IntegralMixedValueHomogeneousMatrix.entry_succ]
  apply IntegralMixedValueHomogeneousSource.value_succ
    (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)
    (fun _ => reply (query P F q)) q j k r t
  intro HH
  have HQ : IntegralMixedValueHomogeneousRequest.request P F q := by
    change HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)
    rw [HP]
    exact HH
  have HZ : get P .slot8 q ≠ 0 := by rw [hs]; exact Nat.succ_ne_zero j.val
  change reply (query P F q) = _
  rw [he HQ]
  unfold currentValue
  rw [ite_eq_right HZ, query, ite_eq_right HZ]
  exact IntegralMixedValueHomogeneousChildren.coordinate_reply P F g q j k r t hs hk hr ht HQ

end LeanCanny.Algebra.IntegralMixedValueHomogeneousPoint
