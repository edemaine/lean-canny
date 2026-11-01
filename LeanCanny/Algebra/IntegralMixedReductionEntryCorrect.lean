/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedReductionEntry
/-! # Charged reduction entries equal the actual integer matrix block -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedReductionEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatReductionEntryBits (Source packet lowerInput)
open IntegralPurePowerActionBits (reductionSource)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] program IntegralCriticalFlatReductionEntryBits.packet

theorem value_block (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (q : List Bool)
    (hl : PurePowerReductionBits.Charged.scalar (IntegralPurePowerReductionBits.layout S)
        (IntegralPurePowerReductionBits.writer S (packet P S q)) →
      answer (IntegralMixedScalarQueryBits.commonLeading P q) = a.leading q)
    (he : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout S)
        (fun z => S.layout.bound (pairFst z)) (IntegralPurePowerReductionBits.writer S (packet P S q)) →
      answer (IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S q))) =
        a.low (lowerInput S (packet P S q)))
    (i j : Fin ((reductionSource S).dimension q * S.rank q))
    (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (program P S).value answer q =
      letI := S.ring q
      residueBits ((IntegralCoefficientBlocks.blockHom (S.basis q) ((reductionSource S).dimension q)
        ((reductionSource S).matrix q) i j : ℤ) : ZMod (S.modulus q)) := by
  let := S.ring q
  rw [value_at P S a answer q hl he]
  have HP : packet P S q = IntegralReductionActionBits.packet q
      i.divNat.val j.divNat.val i.modNat.val j.modNat.val := by
    simp only [IntegralCriticalFlatReductionEntryBits.packet, IntegralCriticalFlatActionBits.packet,
      IntegralCriticalFlatRelativeFactorBits.packet, IntegralBerkowitzBlockBits.outerPacket,
      MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hi, hj]
    rfl
  rw [HP]
  have HE := IntegralPurePowerReductionBits.entry_correct S a q i.divNat j.divNat i.modNat j.modNat
  have HB := IntegralCoefficientBlocks.block_entry (S.basis q) ((reductionSource S).matrix q)
    i.divNat j.divNat i.modNat j.modNat
  have HI : finProdFinEquiv (i.divNat, i.modNat) = i := finProdFinEquiv.apply_symm_apply i
  have HJ : finProdFinEquiv (j.divNat, j.modNat) = j := finProdFinEquiv.apply_symm_apply j
  rw [HI, HJ] at HB
  exact HE.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (S.modulus q))) HB.symm)

end LeanCanny.Algebra.IntegralMixedReductionEntryBits
