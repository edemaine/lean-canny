/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryClosure
/-! # PSC matrices preserve the literal parent, coordinate and finite index -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntrySnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedSquarefreeMatrixSource.matrix

noncomputable def indices (F : Family) (j : ℕ) : IntegralMixedVirtualSweepSource.Indices F where
  coordinate key := ⟨j % (F.ambient key - (F.rule key).critical.offset.val + 1), Nat.mod_lt _ (by omega)⟩
  coefficientIndex _ := 0
  target _ := 0
  row key := ⟨0, Nat.pow_pos (Nat.two_pow_pos _)⟩
  col key := ⟨0, Nat.pow_pos (Nat.two_pow_pos _)⟩
  modulus _ := 1
  modulus_ne_zero _ := by decide
noncomputable def index (F : Family) (c : ℕ) (key : List Bool) :
    Fin (IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial key) (F.rule key)) :=
  ⟨c % IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial key) (F.rule key),
    Nat.mod_lt _ (Nat.pow_pos (Nat.two_pow_pos _))⟩
noncomputable def source (F : Family) (j c : ℕ) : IntegralBerkowitzBlockBits.Source :=
  IntegralMixedSquarefreeNativeSource.source F (indices F j) (index F c)
noncomputable def table (F : Family) (key : List Bool) (j c a b r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (fun u v => IntegralCriticalTotalSnapshotBits.integerEntry ((source F j c).entryMatrix key u v) r t) a b

theorem snapshot (P : Parameters) (F : Family) (q : List Bool) (a b r t : ℕ) :
    IntegralMixedPscEntryBits.table P F q a b r t = table F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) a b r t := rfl

theorem transport (P : Parameters) (F : Family) (q z : List Bool) (a b r t : ℕ)
    (hs : IntegralMixedVirtualTaskBits.saved P z = IntegralMixedVirtualTaskBits.saved P q)
    (hj : get P .slot13 z = get P .slot13 q) (hc : get P .slot8 z = get P .slot8 q) :
    IntegralMixedPscEntryBits.table P F z a b r t = IntegralMixedPscEntryBits.table P F q a b r t := by
  rw [snapshot, snapshot, hs, hj, hc]

theorem value_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPscEntryBits.value P F q = residueBits (table F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) (get P .slot9 q) (get P .slot10 q)
      (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl

end LeanCanny.Algebra.IntegralMixedPscEntrySnapshot
