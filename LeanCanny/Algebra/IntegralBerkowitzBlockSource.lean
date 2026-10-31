/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockMomentSpace
public import LeanCanny.Algebra.BerkowitzFactorChildCorrect

/-! # Original coefficient-block sources for relative Berkowitz evaluation

The source matrix has entries in the actual parameter algebra. Its reader
returns one integer multiplication-matrix entry. All source and basis ranks
remain binary, and query fields retain the original source record.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Source where
  dimension : List Bool → ℕ
  rank : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  nontrivial : ∀ c, Nontrivial (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  matrix : ∀ c, Matrix (Fin (dimension c)) (Fin (dimension c)) (carrier c)
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  coefficient : List Bool → ℕ
  basisRow : ∀ c, Fin (rank c)
  basisCol : ∀ c, Fin (rank c)

theorem Source.rank_pos (S : Source) (c : List Bool) : 0 < S.rank c :=
  (Nat.zero_le _).trans_lt (S.basisRow c).isLt

noncomputable def Source.entryMatrix (S : Source) (c : List Bool) (i j : Fin (S.dimension c)) :
    Matrix (Fin (S.rank c)) (Fin (S.rank c)) ℤ := by
  letI := S.ring c
  exact Algebra.leftMulMatrix (S.basis c) (S.matrix c i j)

noncomputable def Source.coefficientMatrix (S : Source) (c : List Bool) (k : ℕ) :
    Matrix (Fin (S.rank c)) (Fin (S.rank c)) ℤ := by
  letI := S.ring c
  exact Algebra.leftMulMatrix (S.basis c) ((S.matrix c).charpoly.coeff k)

noncomputable def Source.value (S : Source) (c : List Bool) : List Bool :=
  residueBits ((S.coefficientMatrix c (S.coefficient c) (S.basisRow c) (S.basisCol c) : ℤ) : ZMod (S.modulus c))

structure Access (S : Source) where
  dimension : BinaryFn S.dimension
  rank : BinaryFn S.rank
  modulus : BinaryFn S.modulus
  coefficient : BinaryFn S.coefficient
  basisRow : BinaryFn (fun c => (S.basisRow c).val)
  basisCol : BinaryFn (fun c => (S.basisCol c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c (i j : Fin (S.dimension c)) (r t : Fin (S.rank c)),
    entry (pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((S.entryMatrix c i j r t : ℤ) : ZMod (S.modulus c))

def original (p : List Bool) : List Bool := pairFst (pairFst p)
def basisRowCode (p : List Bool) : List Bool := pairFst (pairSnd (pairFst p))
def basisColCode (p : List Bool) : List Bool := pairSnd (pairSnd (pairFst p))

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem basisRowCode_FP : basisRowCode ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem basisColCode_FP : basisColCode ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def stage (S : Source) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p) / (S.dimension (original p) + 1)
def targetStage (S : Source) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p) / (S.dimension (original p) + 1)
def sourceDegree (S : Source) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p) % (S.dimension (original p) + 1)
def targetDegree (S : Source) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p) % (S.dimension (original p) + 1)
def remaining (S : Source) (p : List Bool) : ℕ := S.dimension (original p) - stage S p - 1
def momentExponent (S : Source) (p : List Bool) : ℕ := targetDegree S p - (sourceDegree S p + 1)

theorem originalDimension_binary (S : Source) (a : Access S) :
    BinaryFn (fun p => S.dimension (original p)) := a.dimension.comp original_FP
theorem originalRank_binary (S : Source) (a : Access S) :
    BinaryFn (fun p => S.rank (original p)) := a.rank.comp original_FP

theorem stage_binary (S : Source) (a : Access S) : BinaryFn (stage S) :=
  (BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP).div
    ((originalDimension_binary S a).add (BinaryFn.const 1))
theorem targetStage_binary (S : Source) (a : Access S) : BinaryFn (targetStage S) :=
  (BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP).div
    ((originalDimension_binary S a).add (BinaryFn.const 1))
theorem sourceDegree_binary (S : Source) (a : Access S) : BinaryFn (sourceDegree S) :=
  (BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP).mod
    ((originalDimension_binary S a).add (BinaryFn.const 1))
theorem targetDegree_binary (S : Source) (a : Access S) : BinaryFn (targetDegree S) :=
  (BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP).mod
    ((originalDimension_binary S a).add (BinaryFn.const 1))
theorem remaining_binary (S : Source) (a : Access S) : BinaryFn (remaining S) :=
  ((originalDimension_binary S a).sub (stage_binary S a)).sub (BinaryFn.const 1)
theorem momentExponent_binary (S : Source) (a : Access S) : BinaryFn (momentExponent S) :=
  (targetDegree_binary S a).sub ((sourceDegree_binary S a).add (BinaryFn.const 1))

def basisIndex (S : Source) (word : List Bool → List Bool) (p : List Bool) : Fin (S.rank (original p)) :=
  ⟨Nat.fromBitsLE (word p) % S.rank (original p), Nat.mod_lt _ (S.rank_pos _)⟩

theorem basisIndex_binary (S : Source) (a : Access S) (word : List Bool → List Bool) (hw : word ∈ FP) :
    BinaryFn (fun p => (basisIndex S word p).val) :=
  (BinaryFn.fromBits hw).mod (originalRank_binary S a)

end LeanCanny.Algebra.IntegralBerkowitzBlockBits
