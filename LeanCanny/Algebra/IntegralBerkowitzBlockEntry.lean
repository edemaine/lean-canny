/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockFactorCorrect

/-! # Native entries of the integer relative-Berkowitz power matrix

The old basis rank is the low block digit. The outer selector evaluates
the original algebra-valued coefficient transformation; its integer block
entry is therefore read from the original matrix source.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def powerDimension (S : Source) (c : List Bool) : ℕ := IntegralCoefficientBlocks.dimension (S.dimension c) (S.rank c)

noncomputable def Source.powerMatrix (S : Source) (c : List Bool) :
    Matrix (Fin (powerDimension S c)) (Fin (powerDimension S c)) ℤ := by
  letI := S.ring c
  exact IntegralCoefficientBlocks.blockHom (S.basis c) ((S.dimension c + 1) * (S.dimension c + 1))
    (Berkowitz.powerMatrix (S.matrix c))

attribute [local irreducible] Berkowitz.powerMatrix

def outerPacket (S : Source) (q : List Bool) : List Bool :=
  let c := pairFst q
  let i := Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex q)
  let j := Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex q)
  pair (IntegralBlockMomentBits.context c (i % S.rank c) (j % S.rank c))
    (pair (BinaryNatCode.encode (i / S.rank c)) (BinaryNatCode.encode (j / S.rank c)))

theorem outerPacket_FP (S : Source) (a : Access S) : outerPacket S ∈ FP := by
  have hM : BinaryFn (fun q => S.rank (pairFst q)) := a.rank.comp pairFst_mem_FP
  have hi : BinaryFn (fun q => Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex q)) :=
    BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP
  have hj : BinaryFn (fun q => Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex q)) :=
    BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair (hi.mod hM).bits_mem_FP (hj.mod hM).bits_mem_FP))
    (mem_FP_pair (hi.div hM).bits_mem_FP (hj.div hM).bits_mem_FP)

theorem outer_packet (S : Source) (c : List Bool) (i j : Fin (powerDimension S c)) :
    outerPacket S (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (IntegralBlockMomentBits.context c i.modNat.val j.modNat.val)
        (pair (BinaryNatCode.encode i.divNat.val) (BinaryNatCode.encode j.divNat.val)) := by
  simp only [outerPacket, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem reference_packet (S : Source) (c : List Bool)
    (i j : Fin ((S.dimension c + 1) * (S.dimension c + 1))) (r t : Fin (S.rank c)) :
    letI := S.ring c
    referenceValue S (pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) (Berkowitz.powerMatrix (S.matrix c) i j) r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  generalize hz : pair (IntegralBlockMomentBits.context c r.val t.val)
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) = p
  have ho : original p = c := by
    rw [original, ← hz]
    simp only [IntegralBlockMomentBits.context, pairFst_pair]
  have hr : (basisIndex S basisRowCode p).val = r.val := by
    change Nat.fromBitsLE (basisRowCode p) % S.rank (original p) = r.val
    rw [← hz]
    simp only [basisRowCode, original, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt r.isLt]
  have hc : (basisIndex S basisColCode p).val = t.val := by
    change Nat.fromBitsLE (basisColCode p) % S.rank (original p) = t.val
    rw [← hz]
    simp only [basisColCode, original, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt t.isLt]
  have hs : stage S p = i.divNat.val := by
    change stage S p = i.val / (S.dimension c + 1)
    rw [stage, ← hz]
    simp only [original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have ht : targetStage S p = j.divNat.val := by
    change targetStage S p = j.val / (S.dimension c + 1)
    rw [targetStage, ← hz]
    simp only [original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hd : sourceDegree S p = i.modNat.val := by
    change sourceDegree S p = i.val % (S.dimension c + 1)
    rw [sourceDegree, ← hz]
    simp only [original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hk : targetDegree S p = j.modNat.val := by
    change targetDegree S p = j.val % (S.dimension c + 1)
    rw [targetDegree, ← hz]
    simp only [original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  have HR : basisIndex S basisRowCode p = r := Fin.ext hr
  have HC : basisIndex S basisColCode p = t := Fin.ext hc
  change coefficientValue S p (Berkowitz.FactorChild.value (S.matrix (original p))
    (stage S p) (targetStage S p) (sourceDegree S p) (targetDegree S p)) = _
  rw [hs, ht, hd, hk, Berkowitz.FactorChild.value_eq_powerMatrix (S.matrix (original p)) i j]
  unfold coefficientValue
  rw [HR, HC]

noncomputable def entryProgram (S : Source) (a : Access S) : List Bool → List Bool := factorValue S a ∘ outerPacket S

theorem entry_evaluator (S : Source) (a : Access S) (E : SpaceFunction a.entry) : SpaceFunction (entryProgram S a) :=
  (factor_evaluator S a E).precompose (outerPacket S) (outerPacket_FP S a)

theorem entry_correct (S : Source) (a : Access S) (c : List Bool) (i j : Fin (powerDimension S c)) :
    entryProgram S a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  rw [entryProgram, Function.comp_apply, factor_reference, outer_packet, reference_packet]
  have HB := IntegralCoefficientBlocks.block_entry (S.basis c) (Berkowitz.powerMatrix (S.matrix c))
    i.divNat j.divNat i.modNat j.modNat
  have HI : finProdFinEquiv (i.divNat, i.modNat) = i := finProdFinEquiv.apply_symm_apply i
  have HJ : finProdFinEquiv (j.divNat, j.modNat) = j := finProdFinEquiv.apply_symm_apply j
  rw [HI, HJ] at HB
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (S.modulus c))) HB.symm

end LeanCanny.Algebra.IntegralBerkowitzBlockBits
