/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockSource

/-! # Algebra-valued matrix-power coefficient sources

Only the original multiplication-matrix entries are supplied. Outer matrix
indices and old basis ranks have separate binary fields; the original
record and its requested modulus remain unchanged in every entry query.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockPowerBits
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
  matrix : ∀ c, Matrix (Fin (dimension c)) (Fin (dimension c)) (carrier c)
  exponent : List Bool → ℕ
  row : ∀ c, Fin (dimension c)
  col : ∀ c, Fin (dimension c)
  basisRow : ∀ c, Fin (rank c)
  basisCol : ∀ c, Fin (rank c)
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool := by
  letI := F.ring c
  exact residueBits ((Algebra.leftMulMatrix (F.basis c)
    ((F.matrix c ^ F.exponent c) (F.row c) (F.col c)) (F.basisRow c) (F.basisCol c) : ℤ) : ZMod (F.modulus c))

structure Access (F : Family) where
  dimension : BinaryFn F.dimension
  rank : BinaryFn F.rank
  exponent : BinaryFn F.exponent
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  basisRow : BinaryFn (fun c => (F.basisRow c).val)
  basisCol : BinaryFn (fun c => (F.basisCol c).val)
  modulus : BinaryFn F.modulus
  entry : List Bool → List Bool
  entry_eq : ∀ c (i j : Fin (F.dimension c)) (r t : Fin (F.rank c)),
    letI := F.ring c
    entry (pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((Algebra.leftMulMatrix (F.basis c) (F.matrix c i j) r t : ℤ) : ZMod (F.modulus c))

noncomputable def Family.powerMatrix (F : Family) (c : List Bool) :
    Matrix (Fin (F.dimension c * F.rank c)) (Fin (F.dimension c * F.rank c)) ℤ := by
  letI := F.ring c
  exact IntegralCoefficientBlocks.blockHom (F.basis c) (F.dimension c) (F.matrix c)

def outerPacket (F : Family) (q : List Bool) : List Bool :=
  let c := pairFst q
  let i := Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex q)
  let j := Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex q)
  pair (IntegralBlockMomentBits.context c (i % F.rank c) (j % F.rank c))
    (pair (BinaryNatCode.encode (i / F.rank c)) (BinaryNatCode.encode (j / F.rank c)))

theorem outerPacket_FP (F : Family) (a : Access F) : outerPacket F ∈ FP := by
  have hM : BinaryFn (fun q => F.rank (pairFst q)) := a.rank.comp pairFst_mem_FP
  have hi : BinaryFn (fun q => Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex q)) :=
    BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP
  have hj : BinaryFn (fun q => Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex q)) :=
    BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair (hi.mod hM).bits_mem_FP (hj.mod hM).bits_mem_FP))
    (mem_FP_pair (hi.div hM).bits_mem_FP (hj.div hM).bits_mem_FP)

def entryProgram (F : Family) (a : Access F) : List Bool → List Bool := a.entry ∘ outerPacket F

theorem entry_evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction (entryProgram F a) :=
  E.precompose (outerPacket F) (outerPacket_FP F a)

theorem entry_correct (F : Family) (a : Access F) (c : List Bool)
    (i j : Fin (F.dimension c * F.rank c)) :
    entryProgram F a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c)) := by
  let := F.ring c
  have HP : outerPacket F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (IntegralBlockMomentBits.context c i.modNat.val j.modNat.val)
        (pair (BinaryNatCode.encode i.divNat.val) (BinaryNatCode.encode j.divNat.val)) := by
    simp only [outerPacket, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  rw [entryProgram, Function.comp_apply, HP, a.entry_eq]
  have HB := IntegralCoefficientBlocks.block_entry (F.basis c) (F.matrix c) i.divNat j.divNat i.modNat j.modNat
  have HI : finProdFinEquiv (i.divNat, i.modNat) = i := finProdFinEquiv.apply_symm_apply i
  have HJ : finProdFinEquiv (j.divNat, j.modNat) = j := finProdFinEquiv.apply_symm_apply j
  rw [HI, HJ] at HB
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) HB.symm

end LeanCanny.Algebra.IntegralBlockPowerBits
