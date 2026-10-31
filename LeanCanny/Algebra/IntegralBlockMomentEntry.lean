/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoefficientBlocks
public import LeanCanny.Algebra.MatrixMomentSpaceEntries
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Native entry routing for algebra-valued matrix moments

An augmented moment entry reads one original row, column, or matrix block.
The integer index is split into its outer vertex and old basis index using
binary division and remainder. Native space charges include all three
original readers. Semantic identification with the block matrix is separate.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Family where
  dimension : List Bool → ℕ
  rank : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  row : ∀ c, Fin (dimension c) → carrier c
  column : ∀ c, Fin (dimension c) → carrier c
  matrix : ∀ c, Matrix (Fin (dimension c)) (Fin (dimension c)) (carrier c)
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  exponent : List Bool → ℕ
  basisRow : ∀ c, Fin (rank c)
  basisCol : ∀ c, Fin (rank c)

noncomputable def Family.rowMatrix (F : Family) (c : List Bool) (i : Fin (F.dimension c)) :
    Matrix (Fin (F.rank c)) (Fin (F.rank c)) ℤ := by
  letI := F.ring c
  exact Algebra.leftMulMatrix (F.basis c) (F.row c i)

noncomputable def Family.columnMatrix (F : Family) (c : List Bool) (i : Fin (F.dimension c)) :
    Matrix (Fin (F.rank c)) (Fin (F.rank c)) ℤ := by
  letI := F.ring c
  exact Algebra.leftMulMatrix (F.basis c) (F.column c i)

noncomputable def Family.entryMatrix (F : Family) (c : List Bool) (i j : Fin (F.dimension c)) :
    Matrix (Fin (F.rank c)) (Fin (F.rank c)) ℤ := by
  letI := F.ring c
  exact Algebra.leftMulMatrix (F.basis c) (F.matrix c i j)

def context (c : List Bool) (i j : ℕ) : List Bool := pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))

structure Access (F : Family) where
  dimension : BinaryFn F.dimension
  rank : BinaryFn F.rank
  modulus : BinaryFn F.modulus
  exponent : BinaryFn F.exponent
  basisRow : BinaryFn (fun c => (F.basisRow c).val)
  basisCol : BinaryFn (fun c => (F.basisCol c).val)
  row : List Bool → List Bool
  column : List Bool → List Bool
  entry : List Bool → List Bool
  row_eq : ∀ c (i : Fin (F.dimension c)) (r t : Fin (F.rank c)),
    row (pair (context c r.val t.val) (BinaryNatCode.encode i.val)) =
      residueBits ((F.rowMatrix c i r t : ℤ) : ZMod (F.modulus c))
  column_eq : ∀ c (i : Fin (F.dimension c)) (r t : Fin (F.rank c)),
    column (pair (context c r.val t.val) (BinaryNatCode.encode i.val)) =
      residueBits ((F.columnMatrix c i r t : ℤ) : ZMod (F.modulus c))
  entry_eq : ∀ c (i j : Fin (F.dimension c)) (r t : Fin (F.rank c)),
    entry (pair (context c r.val t.val) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((F.entryMatrix c i j r t : ℤ) : ZMod (F.modulus c))

def bitsAccess (F : Family) (a : Access F) : MatrixMoment.EntryBits.Access where
  dimension q := BinaryNatCode.encode (F.dimension (pairFst q))
  row := a.row
  column := a.column
  entry := a.entry

def outerPacket (F : Family) (q : List Bool) : List Bool :=
  let c := pairFst q
  let i := Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex q)
  let j := Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex q)
  pair (context c (i % F.rank c) (j % F.rank c))
    (pair (BinaryNatCode.encode (i / F.rank c)) (BinaryNatCode.encode (j / F.rank c)))

theorem outerPacket_FP (F : Family) (a : Access F) : outerPacket F ∈ FP := by
  have hM : BinaryFn (fun q => F.rank (pairFst q)) := a.rank.comp pairFst_mem_FP
  have hi : BinaryFn (fun q => Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex q)) :=
    BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP
  have hj : BinaryFn (fun q => Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex q)) :=
    BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair (hi.mod hM).bits_mem_FP (hj.mod hM).bits_mem_FP))
    (mem_FP_pair (hi.div hM).bits_mem_FP (hj.div hM).bits_mem_FP)

def entryProgram (F : Family) (a : Access F) : List Bool → List Bool :=
  MatrixMoment.EntryBits.entry (bitsAccess F a) ∘ outerPacket F

theorem entry_evaluator (F : Family) (a : Access F)
    (R : SpaceFunction a.row) (C : SpaceFunction a.column) (E : SpaceFunction a.entry) :
    SpaceFunction (entryProgram F a) := by
  have hD : BinaryFn (fun q => F.dimension (pairFst q)) := a.dimension.comp pairFst_mem_FP
  exact (MatrixMoment.EntryBits.entryEvaluator (bitsAccess F a) hD.bits_mem_FP R C E).precompose
    (outerPacket F) (outerPacket_FP F a)

end LeanCanny.Algebra.IntegralBlockMomentBits
