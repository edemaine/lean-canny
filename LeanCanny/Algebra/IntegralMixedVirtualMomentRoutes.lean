/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMomentEntry
public import LeanCanny.Algebra.IntegralMixedVirtualActionModel
/-! # Typed virtual action requests retain both old-basis indices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

theorem actionChild_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin ((characteristic P F).dimension q)) (r t : Fin ((characteristic P F).rank q)) :
    IntegralMixedVirtualMatrixBits.actionEntry P F (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F)
      (pair (IntegralBlockMomentBits.context q r.val t.val) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).entryMatrix q i j r t : ℤ) : ZMod ((characteristic P F).modulus q)) := by
  let := (characteristic P F).ring q
  let u : Fin ((characteristic P F).dimension q * (characteristic P F).rank q) := finProdFinEquiv (i, r)
  let v : Fin ((characteristic P F).dimension q * (characteristic P F).rank q) := finProdFinEquiv (j, t)
  have HP : IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic P F)
      (pair (IntegralBlockMomentBits.context q r.val t.val) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        pair q (pair (BinaryNatCode.encode u.val) (BinaryNatCode.encode v.val)) := by
    simp only [IntegralCriticalFlatBerkowitzQuery.entryPacket, original, IntegralBlockMomentBits.context,
      basisRowCode, basisColCode, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  change IntegralMixedVirtualMatrixBits.actionEntry P F (IntegralCriticalFlatMatrixQuery.writer P .actionEntry _) = _
  rw [HP]
  have HV := action_child P F g q hv u v
  have HE : IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic P F) q u v =
      (characteristic P F).entryMatrix q i j r t :=
    IntegralCoefficientBlocks.block_entry ((characteristic P F).basis q) ((characteristic P F).matrix q) i j r t
  have HM : (characteristic P F).modulus q = modulus P q := rfl
  exact HV.trans ((congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) HE).trans
    (congrArg (fun m => residueBits (((characteristic P F).entryMatrix q i j r t : ℤ) : ZMod m)) HM.symm))

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits
