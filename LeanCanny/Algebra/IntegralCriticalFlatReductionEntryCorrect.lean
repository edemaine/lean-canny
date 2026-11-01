/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatReductionEntry
/-! # Finite flat reduction entries equal their integer matrix blocks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatReductionEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralPurePowerActionBits (reductionSource)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem value_block (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool)
    (he : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout S)
      (fun z => S.layout.bound (pairFst z)) (IntegralPurePowerReductionBits.writer S (packet P S c)) →
      answer (IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S c))) = a.low (lowerInput S (packet P S c)))
    (i j : Fin ((reductionSource S).dimension c * S.rank c))
    (hi : get P .row c = i.val) (hj : get P .col c = j.val) :
    (program P S a).value answer c =
      letI := S.ring c
      residueBits ((IntegralCoefficientBlocks.blockHom (S.basis c) ((reductionSource S).dimension c)
        ((reductionSource S).matrix c) i j : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  rw [value P S a answer c he]
  have HP : packet P S c = IntegralReductionActionBits.packet c
      i.divNat.val j.divNat.val i.modNat.val j.modNat.val := by
    simp only [packet, IntegralCriticalFlatActionBits.packet, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBerkowitzBlockBits.outerPacket, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hi, hj]
    rfl
  rw [HP]
  have HE := IntegralPurePowerReductionBits.entry_correct S a c i.divNat j.divNat i.modNat j.modNat
  have HB := IntegralCoefficientBlocks.block_entry (S.basis c) ((reductionSource S).matrix c)
    i.divNat j.divNat i.modNat j.modNat
  have HI : finProdFinEquiv (i.divNat, i.modNat) = i := finProdFinEquiv.apply_symm_apply i
  have HJ : finProdFinEquiv (j.divNat, j.modNat) = j := finProdFinEquiv.apply_symm_apply j
  rw [HI, HJ] at HB
  exact HE.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (S.modulus c))) HB.symm)

end LeanCanny.Algebra.IntegralCriticalFlatReductionEntryBits
