/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueRowCorrect
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStageLocal
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot

/-! # The actual negative Gram characteristic source and native metadata

The mathematical entry table supplies the reference semantics for later
resumable stages. It is not assumed computable. Only source dimensions,
modulus, coefficient and basis selectors receive native FP certificates.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramCharacteristicSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralBerkowitzBlockBits
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis
attribute [local irreducible] residueBits

noncomputable def zeroChoice (F : Family) (q : List Bool) :
    Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)) :=
  ⟨0, by change 0 < IntegralMixedGridValue.dimension (F.spatial q) (F.rule q) + 2; omega⟩
noncomputable def baseSource (P : Parameters) (F : Family) : Source :=
  IntegralMixedValueDeterminantSource.source (IntegralMixedVirtualTaskBits.family P F)
    (IntegralMixedVirtualTaskBits.indices P F) (zeroChoice (IntegralMixedVirtualTaskBits.family P F))

theorem rank_pos (P : Parameters) (F : Family) (q : List Bool) :
    0 < IntegralMixedValueGramSumSource.rank P F q := Nat.pow_pos (Nat.two_pow_pos _)
noncomputable def basisIndex (P : Parameters) (F : Family) (f : Field) (q : List Bool) :
    Fin (IntegralMixedValueGramSumSource.rank P F q) :=
  ⟨get P f q % IntegralMixedValueGramSumSource.rank P F q, Nat.mod_lt _ (rank_pos P F q)⟩

noncomputable def source (P : Parameters) (F : Family) : Source :=
  { baseSource P F with basisRow := basisIndex P F .row, basisCol := basisIndex P F .col }

theorem source_modulus (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).modulus q = modulus P q := rfl

theorem source_entry (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) (r t : Fin ((source P F).rank q)) :
    (source P F).entryMatrix q i j r t = IntegralMixedValueGramSumSource.entry P F q i j r t := by
  have H : (source P F).entryMatrix q i j r t = (baseSource P F).entryMatrix q i j r t := rfl
  exact H.trans (IntegralMixedValueGramEntry.source_entry (IntegralMixedVirtualTaskBits.family P F)
    (IntegralMixedVirtualTaskBits.indices P F) (zeroChoice (IntegralMixedVirtualTaskBits.family P F)) q i j r t)

noncomputable def table (P : Parameters) (F : Family) (q : List Bool) (i j r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r t) i j

theorem table_finite (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) (r t : Fin ((source P F).rank q)) :
    table P F q i.val j.val r.val t.val = (source P F).entryMatrix q i j r t := by
  exact (IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (show Matrix (Fin ((source P F).dimension q)) (Fin ((source P F).dimension q)) ℤ from
      fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r.val t.val) i j).trans
        (IntegralCriticalTotalSnapshotBits.integerEntry_fin ((source P F).entryMatrix q i j) r t)

noncomputable def encodeInteger (m : ℕ) (z : ℤ) : List Bool := residueBits (z : ZMod m)

theorem encodeInteger_eq (m : ℕ) (z : ℤ) : encodeInteger m z = residueBits (z : ZMod m) := rfl

noncomputable def entryBits (P : Parameters) (F : Family) (z : List Bool) : List Bool :=
  encodeInteger ((source P F).modulus (original z)) (table P F (original z)
    (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex z)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex z))
    (Nat.fromBitsLE (basisRowCode z)) (Nat.fromBitsLE (basisColCode z)))

attribute [local irreducible] encodeInteger

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
  dimension := IntegralMixedValueGramSumSource.columns_binary P a F h
  rank := IntegralMixedValueGramProductTasks.rank_binary P a F h
  modulus := modulus_binary P a
  coefficient := BinaryFn.const 0
  basisRow := (get_binary P a .row).mod (IntegralMixedValueGramProductTasks.rank_binary P a F h)
  basisCol := (get_binary P a .col).mod (IntegralMixedValueGramProductTasks.rank_binary P a F h)
  entry := entryBits P F
  entry_eq := entry_packet P F

end LeanCanny.Algebra.IntegralMixedGramCharacteristicSource
