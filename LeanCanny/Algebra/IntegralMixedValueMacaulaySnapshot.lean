/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramProductTasks

/-! # Literal selected-parent snapshots for rectangular Gram factors -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulaySnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

noncomputable def pointAt (F : Family) (key : List Bool) (j a b r t : ℕ) : ℤ :=
  IntegralMixedValueMacaulayMatrix.totalEntry F (IntegralMixedValueHomogeneousSnapshot.pointIndices F j) key a b r t

theorem entry_pull (F : Family) (Q : Queries) (base : List Bool → List Bool) (q : List Bool)
    (a : Fin (IntegralMixedValueMacaulayMatrix.rows F (base q)))
    (b : Fin (IntegralMixedValueMacaulayMatrix.columns F (base q)))
    (r t : Fin (IntegralMixedValueMacaulayMatrix.rank F (base q))) :
    IntegralMixedValueMacaulayMatrix.entry (pull F base) (IntegralMixedVirtualQueryBits.indices (pull F base) Q) q a b r t =
      IntegralMixedValueMacaulayMatrix.entry F (IntegralMixedValueHomogeneousSnapshot.pointIndices F (Q.coordinate q))
        (base q) a b r t := by
  let read (p : Fin (IntegralMixedValueMacaulayMatrix.arity F (base q)) →
      MvPolynomial (Fin (IntegralMixedValueMacaulayMatrix.arity F (base q)))
        (IntegralMixedValueDoubleNilpotent.Second (F.state (base q)))) : ℤ :=
    Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state (base q)))
      (MacaulayFullBox.matrix p
        (RelativeProjectiveValueGram.degrees
          (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial (base q)) (F.rule (base q)))
            (F.spatial (base q)).degree)
        (IntegralMixedGridValue.width (F.spatial (base q)) (F.rule (base q)))
        ((IntegralMixedValueGramEntry.rowEquiv _ _).symm a) b) r t
  change read (IntegralMixedValueDoubleSystem.mappedSystem (pull F base) q
      ((IntegralMixedVirtualQueryBits.indices (pull F base) Q).coordinate q)) =
    read (IntegralMixedValueDoubleSystem.mappedSystem F (base q)
      ((IntegralMixedValueHomogeneousSnapshot.pointIndices F (Q.coordinate q)).coordinate (base q)))
  apply congrArg read
  funext j
  exact IntegralMixedValueMappedSystemPull.mapped F base q _ j

theorem total_pull (F : Family) (Q : Queries) (base : List Bool → List Bool) (q : List Bool) (a b r t : ℕ) :
    IntegralMixedValueMacaulayMatrix.totalEntry (pull F base) (IntegralMixedVirtualQueryBits.indices (pull F base) Q)
      q a b r t = pointAt F (base q) (Q.coordinate q) a b r t := by
  have HL : IntegralMixedValueMacaulayMatrix.Labels (pull F base) q a b r t ↔
      IntegralMixedValueMacaulayMatrix.Labels F (base q) a b r t := Iff.rfl
  unfold pointAt IntegralMixedValueMacaulayMatrix.totalEntry
  by_cases H : IntegralMixedValueMacaulayMatrix.Labels (pull F base) q a b r t
  · rw [dite_eq_left H, dite_eq_left (HL.mp H)]
    exact entry_pull F Q base q _ _ _ _
  · rw [dite_eq_right H, dite_eq_right (fun h => H (HL.mpr h))]

theorem value_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueMacaulayMatrix.value P F q = residueBits
      (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [IntegralMixedValueMacaulayMatrix.value, total_pull]
  rfl

theorem parent_entry (P : Parameters) (F : Family) (q : List Bool)
    (a : Fin (IntegralMixedValueMacaulayMatrix.rows (IntegralMixedVirtualTaskBits.family P F) q))
    (b : Fin (IntegralMixedValueMacaulayMatrix.columns (IntegralMixedVirtualTaskBits.family P F) q))
    (r t : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q)) :
    pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) a.val b.val r.val t.val =
      IntegralMixedValueMacaulayMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q a b r t := by
  have H := total_pull F (IntegralMixedVirtualTaskBits.queries P) (IntegralMixedVirtualTaskBits.saved P) q a.val b.val r.val t.val
  rw [IntegralMixedValueMacaulayMatrix.total_finite] at H
  exact H.symm

theorem product_child (P : Parameters) (F : Family) (left : Bool) (q : List Bool) :
    IntegralMixedValueMacaulayMatrix.value P F (IntegralMixedValueGramProductTasks.query P F left q) = residueBits
      (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (IntegralMixedValueGramProductTasks.sourceRow P F q) (IntegralMixedValueGramProductTasks.column P left q)
        (IntegralMixedValueGramProductTasks.row P F left q) (IntegralMixedValueGramProductTasks.col P F left q) :
          ZMod (modulus P q)) := by
  rw [value_snapshot, IntegralMixedValueGramProductTasks.query_saved]
  simp only [IntegralMixedValueGramProductTasks.query_get, reduceCtorEq, ite_false, ite_true]
  exact congrArg (fun m : ℕ => residueBits
    (pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
      (IntegralMixedValueGramProductTasks.sourceRow P F q) (IntegralMixedValueGramProductTasks.column P left q)
      (IntegralMixedValueGramProductTasks.row P F left q) (IntegralMixedValueGramProductTasks.col P F left q) : ZMod m))
        (IntegralMixedValueGramProductTasks.query_modulus P F left q)

end LeanCanny.Algebra.IntegralMixedValueMacaulaySnapshot
