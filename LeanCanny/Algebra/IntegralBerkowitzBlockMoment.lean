/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockSource

/-! # Native relative Berkowitz moments from the original matrix reader

Trailing principal blocks use the original source matrix and basis.
Every row, column, and interior block request returns to that source with
its exact basis ranks. The moment dimensions and exponents remain binary.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def momentFamily (S : Source) : IntegralBlockMomentBits.Family where
  dimension := remaining S
  rank p := S.rank (original p)
  carrier p := S.carrier (original p)
  ring p := S.ring (original p)
  basis p := S.basis (original p)
  row p j := S.matrix (original p)
    ⟨stage S p, by have H := j.isLt; dsimp [remaining] at H; omega⟩
    ⟨stage S p + 1 + j.val, by have H := j.isLt; dsimp [remaining] at H; omega⟩
  column p i := S.matrix (original p)
    ⟨stage S p + 1 + i.val, by have H := i.isLt; dsimp [remaining] at H; omega⟩
    ⟨stage S p, by have H := i.isLt; dsimp [remaining] at H; omega⟩
  matrix p i j := S.matrix (original p)
    ⟨stage S p + 1 + i.val, by have H := i.isLt; dsimp [remaining] at H; omega⟩
    ⟨stage S p + 1 + j.val, by have H := j.isLt; dsimp [remaining] at H; omega⟩
  modulus p := S.modulus (original p)
  modulus_ne_zero p := S.modulus_ne_zero (original p)
  exponent := momentExponent S
  basisRow := basisIndex S basisRowCode
  basisCol := basisIndex S basisColCode

def sourceContext (r : List Bool) : List Bool := pair (original (original r)) (pairSnd (pairFst r))
theorem sourceContext_FP : sourceContext ∈ FP :=
  mem_FP_pair (mem_FP_comp (f := original) (g := original) original_FP original_FP)
    (mem_FP_comp (f := pairFst) (g := pairSnd) pairFst_mem_FP pairSnd_mem_FP)

def rowQuery (S : Source) (r : List Bool) : List Bool :=
  pair (sourceContext r) (pair (BinaryNatCode.encode (stage S (original r)))
    (BinaryNatCode.encode (stage S (original r) + 1 + Nat.fromBitsLE (pairSnd r))))
def columnQuery (S : Source) (r : List Bool) : List Bool :=
  pair (sourceContext r) (pair (BinaryNatCode.encode (stage S (original r) + 1 + Nat.fromBitsLE (pairSnd r)))
    (BinaryNatCode.encode (stage S (original r))))
def matrixQuery (S : Source) (r : List Bool) : List Bool :=
  pair (sourceContext r)
    (pair (BinaryNatCode.encode (stage S (original r) + 1 + Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex r)))
      (BinaryNatCode.encode (stage S (original r) + 1 + Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex r))))

theorem rowQuery_FP (S : Source) (a : Access S) : rowQuery S ∈ FP := by
  have hs : BinaryFn (fun r => stage S (original r)) := (stage_binary S a).comp original_FP
  have hi : BinaryFn (fun r => stage S (original r) + 1 + Nat.fromBitsLE (pairSnd r)) :=
    (hs.add (BinaryFn.const 1)).add (BinaryFn.fromBits pairSnd_mem_FP)
  exact mem_FP_pair sourceContext_FP (mem_FP_pair hs.bits_mem_FP hi.bits_mem_FP)

theorem columnQuery_FP (S : Source) (a : Access S) : columnQuery S ∈ FP := by
  have hs : BinaryFn (fun r => stage S (original r)) := (stage_binary S a).comp original_FP
  have hi : BinaryFn (fun r => stage S (original r) + 1 + Nat.fromBitsLE (pairSnd r)) :=
    (hs.add (BinaryFn.const 1)).add (BinaryFn.fromBits pairSnd_mem_FP)
  exact mem_FP_pair sourceContext_FP (mem_FP_pair hi.bits_mem_FP hs.bits_mem_FP)

theorem matrixQuery_FP (S : Source) (a : Access S) : matrixQuery S ∈ FP := by
  have hs : BinaryFn (fun r => stage S (original r) + 1) := by
    have H : BinaryFn (fun r => stage S (original r)) := (stage_binary S a).comp original_FP
    exact H.add (BinaryFn.const 1)
  have hi := hs.add (BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP)
  have hj := hs.add (BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP)
  exact mem_FP_pair sourceContext_FP (mem_FP_pair hi.bits_mem_FP hj.bits_mem_FP)

theorem rowQuery_packet (S : Source) (p : List Bool) (i r t : ℕ) :
    rowQuery S (pair (IntegralBlockMomentBits.context p r t) (BinaryNatCode.encode i)) =
      pair (IntegralBlockMomentBits.context (original p) r t)
        (pair (BinaryNatCode.encode (stage S p)) (BinaryNatCode.encode (stage S p + 1 + i))) := by
  simp only [rowQuery, sourceContext, original, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem columnQuery_packet (S : Source) (p : List Bool) (i r t : ℕ) :
    columnQuery S (pair (IntegralBlockMomentBits.context p r t) (BinaryNatCode.encode i)) =
      pair (IntegralBlockMomentBits.context (original p) r t)
        (pair (BinaryNatCode.encode (stage S p + 1 + i)) (BinaryNatCode.encode (stage S p))) := by
  simp only [columnQuery, sourceContext, original, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem matrixQuery_packet (S : Source) (p : List Bool) (i j r t : ℕ) :
    matrixQuery S (pair (IntegralBlockMomentBits.context p r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      pair (IntegralBlockMomentBits.context (original p) r t)
        (pair (BinaryNatCode.encode (stage S p + 1 + i)) (BinaryNatCode.encode (stage S p + 1 + j))) := by
  simp only [matrixQuery, sourceContext, original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
    MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def momentAccess (S : Source) (a : Access S) : IntegralBlockMomentBits.Access (momentFamily S) where
  dimension := remaining_binary S a
  rank := originalRank_binary S a
  modulus := a.modulus.comp original_FP
  exponent := momentExponent_binary S a
  basisRow := basisIndex_binary S a basisRowCode basisRowCode_FP
  basisCol := basisIndex_binary S a basisColCode basisColCode_FP
  row := a.entry ∘ rowQuery S
  column := a.entry ∘ columnQuery S
  entry := a.entry ∘ matrixQuery S
  row_eq p j r t := by
    change a.entry (rowQuery S (pair (IntegralBlockMomentBits.context p r.val t.val) (BinaryNatCode.encode j.val))) = _
    rw [rowQuery_packet]
    have hs : stage S p < S.dimension (original p) := by have H := j.isLt; dsimp [momentFamily, remaining] at H; omega
    have hj : stage S p + 1 + j.val < S.dimension (original p) := by have H := j.isLt; dsimp [momentFamily, remaining] at H; omega
    exact a.entry_eq (original p) ⟨stage S p, hs⟩ ⟨stage S p + 1 + j.val, hj⟩ r t
  column_eq p i r t := by
    change a.entry (columnQuery S (pair (IntegralBlockMomentBits.context p r.val t.val) (BinaryNatCode.encode i.val))) = _
    rw [columnQuery_packet]
    have hs : stage S p < S.dimension (original p) := by have H := i.isLt; dsimp [momentFamily, remaining] at H; omega
    have hi : stage S p + 1 + i.val < S.dimension (original p) := by have H := i.isLt; dsimp [momentFamily, remaining] at H; omega
    exact a.entry_eq (original p) ⟨stage S p + 1 + i.val, hi⟩ ⟨stage S p, hs⟩ r t
  entry_eq p i j r t := by
    change a.entry (matrixQuery S (pair (IntegralBlockMomentBits.context p r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = _
    rw [matrixQuery_packet]
    have hi : stage S p + 1 + i.val < S.dimension (original p) := by have H := i.isLt; dsimp [momentFamily, remaining] at H; omega
    have hj : stage S p + 1 + j.val < S.dimension (original p) := by have H := j.isLt; dsimp [momentFamily, remaining] at H; omega
    exact a.entry_eq (original p) ⟨stage S p + 1 + i.val, hi⟩ ⟨stage S p + 1 + j.val, hj⟩ r t

theorem moment_evaluator (S : Source) (a : Access S) (E : SpaceFunction a.entry) : SpaceFunction (momentFamily S).value :=
  IntegralBlockMomentBits.evaluator (momentFamily S) (momentAccess S a)
    (E.precompose (rowQuery S) (rowQuery_FP S a)) (E.precompose (columnQuery S) (columnQuery_FP S a))
    (E.precompose (matrixQuery S) (matrixQuery_FP S a))

end LeanCanny.Algebra.IntegralBerkowitzBlockBits
