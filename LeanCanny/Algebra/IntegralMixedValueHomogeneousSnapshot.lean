/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalTasks

/-! # Integer snapshots of the same-parent homogeneous coefficient source

Snapshots expose only the actual parent and natural query indices. Their
integer values retain the original invalid-label guard. This lets a
second-digit selector transport a whole integer entry, without changing
dependent coefficient algebras or their chosen bases during rewriting.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def pointIndices (F : Family) (j : ℕ) :=
  IntegralMixedVirtualQueryBits.indices F (IntegralMixedVirtualSnapshotBits.constantQueries j 0 0 0 0 1 (by decide))

noncomputable def pointAt (F : Family) (key : List Bool) (j s k r t : ℕ) : ℤ :=
  IntegralMixedValueHomogeneousMatrix.totalEntry F (pointIndices F j) key s k r t

theorem total_pull (F : Family) (Q : Queries) (base : List Bool → List Bool) (q : List Bool) (s k r t : ℕ) :
    IntegralMixedValueHomogeneousMatrix.totalEntry (pull F base) (IntegralMixedVirtualQueryBits.indices (pull F base) Q)
      q s k r t = pointAt F (base q) (Q.coordinate q) s k r t := rfl

theorem value_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueHomogeneousMatrix.value P F q = residueBits
      (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (get P .slot8 q) (get P .target q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [IntegralMixedValueHomogeneousMatrix.value, total_pull]
  rfl

theorem parent_entry (P : Parameters) (F : Family) (q : List Bool)
    (s : Fin (IntegralMixedValueHomogeneousMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1))
    (k : Fin (count (IntegralMixedValueHomogeneousMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueHomogeneousMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (r t : Fin (IntegralMixedValueHomogeneousMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q)) :
    pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) s.val k.val r.val t.val =
      IntegralMixedValueHomogeneousMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q s k r t := by
  have H := total_pull F (IntegralMixedVirtualTaskBits.queries P) (IntegralMixedVirtualTaskBits.saved P) q s.val k.val r.val t.val
  rw [IntegralMixedValueHomogeneousMatrix.total_finite] at H
  exact H.symm

theorem reciprocal_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueHomogeneousMatrix.value P F (IntegralMixedValueReciprocalTasks.query P F q) = residueBits
      (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (get P .slot8 q) (get P .target q) (IntegralMixedValueReciprocalTasks.oldRow P F q)
          (IntegralMixedValueReciprocalTasks.oldCol P F q) : ZMod (modulus P q)) := by
  rw [value_snapshot, IntegralMixedValueReciprocalTasks.query_saved]
  simp only [IntegralMixedValueReciprocalTasks.query_get, reduceCtorEq, ite_false, ite_true]
  exact congrArg (fun m : ℕ => residueBits
    (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
      (get P .slot8 q) (get P .target q) (IntegralMixedValueReciprocalTasks.oldRow P F q)
        (IntegralMixedValueReciprocalTasks.oldCol P F q) : ZMod m))
      (IntegralMixedValueReciprocalTasks.query_modulus P F q)

end LeanCanny.Algebra.IntegralMixedValueHomogeneousSnapshot
