/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalMatrix

/-! # The reciprocal child recovers the exact first-prefix basis entries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalChildren
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask IntegralCoordinateBasis
open IntegralMixedCutSource IntegralMixedValueReciprocalTasks
open scoped Classical

theorem oldRow_pair (P : Parameters) (F : Family) (q : List Bool)
    (u : Fin (count ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q)))
    (a : Fin (2 ^ (IntegralMixedVirtualTaskBits.family P F).width q))
    (hr : get P .row q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a)).val) : oldRow P F q = u.val := by
  change get P .row q / 2 ^ (IntegralMixedVirtualTaskBits.family P F).width q = _
  rw [hr]
  exact FixedWidthChartMonomial.pair_div _ _ u a

theorem oldCol_pair (P : Parameters) (F : Family) (q : List Bool)
    (v : Fin (count ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q)))
    (c : Fin (2 ^ (IntegralMixedVirtualTaskBits.family P F).width q))
    (ht : get P .col q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)).val) : oldCol P F q = v.val := by
  change get P .col q / 2 ^ (IntegralMixedVirtualTaskBits.family P F).width q = _
  rw [ht]
  exact FixedWidthChartMonomial.pair_div _ _ v c

theorem packet_eq (P : Parameters) (F : Family) (q : List Bool)
    (s : Fin (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1))
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (u v : Fin (count ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q)))
    (a c : Fin (2 ^ (IntegralMixedVirtualTaskBits.family P F).width q))
    (hs : get P .slot8 q = s.val) (hk : get P .target q = k.val)
    (hr : get P .row q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a)).val)
    (ht : get P .col q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)).val) :
    IntegralMixedValueHomogeneousQueries.packet P q =
      IntegralMixedValueSystemSemantics.packet (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q s k u v a c :=
  IntegralMixedValueHomogeneousChildren.packet_eq P q _ _ _ _ hs hk hr ht

theorem homogeneous_reply (P : Parameters) (F : Family) (q : List Bool)
    (s : Fin (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1))
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (u v : Fin (count ((IntegralMixedVirtualTaskBits.family P F).birth q + 1) ((IntegralMixedVirtualTaskBits.family P F).width q)))
    (a c : Fin (2 ^ (IntegralMixedVirtualTaskBits.family P F).width q))
    (hs : get P .slot8 q = s.val) (hk : get P .target q = k.val)
    (hr : get P .row q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (u, a)).val)
    (ht : get P .col q = (pairIndex ((IntegralMixedVirtualTaskBits.family P F).birth q + 1)
      ((IntegralMixedVirtualTaskBits.family P F).width q) (v, c)).val) :
    IntegralMixedValueHomogeneousMatrix.value P F (query P F q) = residueBits
      (IntegralMixedValueHomogeneousMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q s k u v : ZMod (modulus P q)) := by
  rw [IntegralMixedValueHomogeneousSnapshot.reciprocal_child, hs, hk, oldRow_pair P F q u a hr, oldCol_pair P F q v c ht]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (IntegralMixedValueHomogeneousSnapshot.parent_entry P F q s k u v)

end LeanCanny.Algebra.IntegralMixedValueReciprocalChildren
