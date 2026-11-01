/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryClosure
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStageLocal
public import LeanCanny.Algebra.IntegralMixedValueDeterminantSource
/-! # The negative PSC characteristic source over the same old parent

Its constant characteristic coefficient is the literal PSC determinant.
The entry table below is a mathematical reference, not an evaluator premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralBerkowitzBlockBits
open scoped Classical

noncomputable def source (P : Parameters) (F : Family) : Source :=
  { IntegralMixedPscEntryBits.source P F with
    matrix q := by
      let := (IntegralMixedPscEntryBits.source P F).ring q
      exact -(IntegralMixedPscEntryBits.source P F).matrix q
    modulus := IntegralCriticalHistoryTask.modulus P
    modulus_ne_zero := IntegralCriticalHistoryTask.modulus_ne_zero P
    coefficient _ := 0
    basisRow := (IntegralMixedVirtualTaskBits.indices P F).row
    basisCol := (IntegralMixedVirtualTaskBits.indices P F).col }

theorem source_entry_neg (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) :
    (source P F).entryMatrix q i j = -(IntegralMixedPscEntryBits.source P F).entryMatrix q i j := by
  let := (IntegralMixedPscEntryBits.source P F).ring q
  change Algebra.leftMulMatrix ((IntegralMixedPscEntryBits.source P F).basis q)
    (-(IntegralMixedPscEntryBits.source P F).matrix q i j) = _
  exact map_neg _ _

noncomputable def table (P : Parameters) (F : Family) (q : List Bool) (i j r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r t) i j

theorem integerEntry_neg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry (-M) r t = -IntegralCriticalTotalSnapshotBits.integerEntry M r t := by
  by_cases hr : r < n
  · by_cases ht : t < n
    · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, hr, ht, dite_eq_left, Matrix.neg_apply]
    · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, hr, ht, dite_eq_left, dite_false, neg_zero]
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, hr, dite_false, neg_zero]

theorem table_neg (P : Parameters) (F : Family) (q : List Bool) (i j r t : ℕ) :
    table P F q i j r t = -IntegralMixedPscEntryBits.table P F q i j r t := by
  have H : (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r t) =
      -(fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((IntegralMixedPscEntryBits.source P F).entryMatrix q a b) r t) := by
    funext a b
    let read (M : Matrix (Fin ((source P F).rank q)) (Fin ((source P F).rank q)) ℤ) : ℤ :=
      IntegralCriticalTotalSnapshotBits.integerEntry M r t
    have HE := congrArg read (source_entry_neg P F q a b)
    exact HE.trans (integerEntry_neg ((IntegralMixedPscEntryBits.source P F).entryMatrix q a b) r t)
  let read (M : Matrix (Fin ((source P F).dimension q)) (Fin ((source P F).dimension q)) ℤ) : ℤ :=
    IntegralCriticalTotalSnapshotBits.integerEntry M i j
  exact (congrArg read H).trans (integerEntry_neg
    (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry
      ((IntegralMixedPscEntryBits.source P F).entryMatrix q a b) r t) i j)

noncomputable def encodeInteger (m : ℕ) (z : ℤ) : List Bool := residueBits (z : ZMod m)
theorem encodeInteger_eq (m : ℕ) (z : ℤ) : encodeInteger m z = residueBits (z : ZMod m) := rfl
noncomputable def entryBits (P : Parameters) (F : Family) (z : List Bool) : List Bool :=
  encodeInteger ((source P F).modulus (original z)) (table P F (original z)
    (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex z)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex z))
    (Nat.fromBitsLE (basisRowCode z)) (Nat.fromBitsLE (basisColCode z)))
attribute [local irreducible] encodeInteger

theorem table_finite (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) (r t : Fin ((source P F).rank q)) :
    table P F q i.val j.val r.val t.val = (source P F).entryMatrix q i j r t :=
  (IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r.val t.val) i j).trans
      (IntegralCriticalTotalSnapshotBits.integerEntry_fin ((source P F).entryMatrix q i j) r t)

theorem entry_packet (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) (r t : Fin ((source P F).rank q)) :
    entryBits P F (pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (((source P F).entryMatrix q i j r t : ℤ) : ZMod ((source P F).modulus q)) := by
  rw [← encodeInteger_eq]
  simp only [entryBits, original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
    MatrixMoment.EntryBits.colIndex, basisRowCode, basisColCode, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [table_finite]

noncomputable def access (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (F : Family) (h : InputMetadata F) :
    IntegralBerkowitzBlockBits.Access (source P F) where
  dimension := IntegralMixedPscEntryBits.dimension_binary P a F h
  rank := IntegralMixedPscEntryBits.rank_binary P a F h
  modulus := (modulus_binary P a).of_eq (fun _ => rfl)
  coefficient := (BinaryFn.const 0).of_eq (fun _ => rfl)
  basisRow := (IntegralMixedVirtualTaskBits.metadata P a F h).row.of_eq (fun _ => rfl)
  basisCol := (IntegralMixedVirtualTaskBits.metadata P a F h).col.of_eq (fun _ => rfl)
  entry := entryBits P F
  entry_eq := entry_packet P F

end LeanCanny.Algebra.IntegralMixedPscCharacteristicBits
