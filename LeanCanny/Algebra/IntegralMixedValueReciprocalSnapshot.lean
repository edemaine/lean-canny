/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayTasks
public import LeanCanny.Algebra.IntegralMixedValueMappedSystemPull

/-! # Same-parent integer snapshots for shifted mapped-system coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

noncomputable def pointAt (F : Family) (key : List Bool) (j s k r t : ℕ) : ℤ :=
  IntegralMixedValueReciprocalMatrix.totalEntry F (IntegralMixedValueHomogeneousSnapshot.pointIndices F j) key s k r t

theorem entry_pull (F : Family) (Q : Queries) (base : List Bool → List Bool) (q : List Bool)
    (s : Fin (IntegralMixedValueReciprocalMatrix.free F (base q) + 1))
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free F (base q) + 1)
      (IntegralMixedValueReciprocalMatrix.width F (base q))))
    (r t : Fin (IntegralMixedValueReciprocalMatrix.rank F (base q))) :
    IntegralMixedValueReciprocalMatrix.entry (pull F base) (IntegralMixedVirtualQueryBits.indices (pull F base) Q) q s k r t =
      IntegralMixedValueReciprocalMatrix.entry F (IntegralMixedValueHomogeneousSnapshot.pointIndices F (Q.coordinate q))
        (base q) s k r t := by
  have HI : (IntegralMixedVirtualQueryBits.indices (pull F base) Q).coordinate q =
      (IntegralMixedValueHomogeneousSnapshot.pointIndices F (Q.coordinate q)).coordinate (base q) := rfl
  let read (p : MvPolynomial
      (Fin (IntegralMixedValueReciprocalMatrix.free F (base q) + 1))
      (IntegralMixedValueDoubleNilpotent.Second (F.state (base q)))) : ℤ :=
    Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state (base q)))
      (p.coeff (nativeExponent (Equiv.refl _) (IntegralMixedValueReciprocalMatrix.width F (base q)) k.val)) r t
  change read (IntegralMixedValueDoubleSystem.mappedSystem (pull F base) q
    ((IntegralMixedVirtualQueryBits.indices (pull F base) Q).coordinate q) s) =
      read (IntegralMixedValueDoubleSystem.mappedSystem F (base q)
        ((IntegralMixedValueHomogeneousSnapshot.pointIndices F (Q.coordinate q)).coordinate (base q)) s)
  have HM := IntegralMixedValueMappedSystemPull.mapped F base q
    ((IntegralMixedVirtualQueryBits.indices (pull F base) Q).coordinate q) s
  exact (congrArg read HM).trans (congrArg
    (fun i => read (IntegralMixedValueDoubleSystem.mappedSystem F (base q) i s)) HI)

theorem total_pull (F : Family) (Q : Queries) (base : List Bool → List Bool) (q : List Bool) (s k r t : ℕ) :
    IntegralMixedValueReciprocalMatrix.totalEntry (pull F base) (IntegralMixedVirtualQueryBits.indices (pull F base) Q)
      q s k r t = pointAt F (base q) (Q.coordinate q) s k r t := by
  have HL : IntegralMixedValueReciprocalMatrix.Labels (pull F base) q s k r t ↔
      IntegralMixedValueReciprocalMatrix.Labels F (base q) s k r t := Iff.rfl
  unfold pointAt IntegralMixedValueReciprocalMatrix.totalEntry
  by_cases H : IntegralMixedValueReciprocalMatrix.Labels (pull F base) q s k r t
  · rw [dite_eq_left H, dite_eq_left (HL.mp H)]
    exact entry_pull F Q base q _ _ _ _
  · rw [dite_eq_right H, dite_eq_right (fun h => H (HL.mpr h))]

theorem value_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueReciprocalMatrix.value P F q = residueBits
      (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (get P .slot8 q) (get P .target q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [IntegralMixedValueReciprocalMatrix.value, total_pull]
  rfl

theorem parent_entry (P : Parameters) (F : Family) (q : List Bool)
    (s : Fin (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1))
    (k : Fin (count (IntegralMixedValueReciprocalMatrix.free (IntegralMixedVirtualTaskBits.family P F) q + 1)
      (IntegralMixedValueReciprocalMatrix.width (IntegralMixedVirtualTaskBits.family P F) q)))
    (r t : Fin (IntegralMixedValueReciprocalMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q)) :
    pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) s.val k.val r.val t.val =
      IntegralMixedValueReciprocalMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q s k r t := by
  have H := total_pull F (IntegralMixedVirtualTaskBits.queries P) (IntegralMixedVirtualTaskBits.saved P) q s.val k.val r.val t.val
  rw [IntegralMixedValueReciprocalMatrix.total_finite] at H
  exact H.symm

theorem macaulay_child (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) :
    IntegralMixedValueReciprocalMatrix.value P F (IntegralMixedValueMacaulayTasks.query P F q) = residueBits
      (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (IntegralMixedValueMacaulayTasks.sourceRow P F q) (IntegralMixedValueMacaulayTasks.difference P F q)
          (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [value_snapshot, IntegralMixedValueMacaulayTasks.query_saved]
  simp only [IntegralMixedValueMacaulayTasks.query_get P F g q, reduceCtorEq, ite_false, ite_true]
  exact congrArg (fun m : ℕ => residueBits
    (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
      (IntegralMixedValueMacaulayTasks.sourceRow P F q) (IntegralMixedValueMacaulayTasks.difference P F q)
        (get P .row q) (get P .col q) : ZMod m)) (IntegralMixedValueMacaulayTasks.query_modulus P F q)

end LeanCanny.Algebra.IntegralMixedValueReciprocalSnapshot
