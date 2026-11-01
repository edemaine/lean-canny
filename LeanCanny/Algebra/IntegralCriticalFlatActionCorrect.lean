/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatAction
/-! # Flat action correctness uses only the selected power reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem value_at (P : Parameters) (S : Source) (answer : List Bool → List Bool) (c : List Bool)
    (he : IntegralReductionActionBits.normalGuard S (packet P S c) →
      answer (IntegralCriticalFlatEulerBits.next P .reductionPower c) = (IntegralReductionActionBits.powerFamily S).value (packet P S c)) :
    (program P S).value answer c = IntegralReductionActionBits.entryProgram S (packet P S c) := by
  by_cases h : IntegralReductionActionBits.normalGuard S (packet P S c)
  · simp only [SingleCall.Program.value, program, h, decide_true, ite_true, pairSnd_pair,
      IntegralReductionActionBits.entryProgram, he h]
  · simp only [SingleCall.Program.value, program, h, decide_false, Bool.false_eq_true, ite_false,
      IntegralReductionActionBits.entryProgram]

theorem value_block (P : Parameters) (S : Source) (answer : List Bool → List Bool) (c : List Bool)
    (he : IntegralReductionActionBits.normalGuard S (packet P S c) →
      answer (IntegralCriticalFlatEulerBits.next P .reductionPower c) = (IntegralReductionActionBits.powerFamily S).value (packet P S c))
    (i j : Fin (S.dimension c * S.rank c))
    (hi : get P .row c = i.val) (hj : get P .col c = j.val) :
    letI := S.ring c
    (program P S).value answer c = residueBits ((IntegralCoefficientBlocks.blockHom (S.basis c) (S.dimension c)
      (S.actionMatrix c) i j : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  rw [value_at P S answer c he]
  have HP : packet P S c = IntegralReductionActionBits.packet c
      i.divNat.val j.divNat.val i.modNat.val j.modNat.val := by
    simp only [packet, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBerkowitzBlockBits.outerPacket, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hi, hj]
    rfl
  rw [HP]
  have HE := IntegralReductionActionBits.entry_correct S c i.divNat j.divNat i.modNat j.modNat
  have HB := IntegralCoefficientBlocks.block_entry (S.basis c) (S.actionMatrix c)
    i.divNat j.divNat i.modNat j.modNat
  have HI : finProdFinEquiv (i.divNat, i.modNat) = i := finProdFinEquiv.apply_symm_apply i
  have HJ : finProdFinEquiv (j.divNat, j.modNat) = j := finProdFinEquiv.apply_symm_apply j
  rw [HI, HJ] at HB
  exact HE.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (S.modulus c))) HB.symm)

end LeanCanny.Algebra.IntegralCriticalFlatActionBits
