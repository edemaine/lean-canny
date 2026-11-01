/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalMomentRoutes
public import LeanCanny.Algebra.IntegralMixedPhysicalMomentSnapshot
/-! # The selected relative diagonal child reads the actual action diagonal -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess

theorem diagonal_child (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (p : List Bool)
    (hd : selector (characteristic P F) p = [false, true]) :
    IntegralMixedPhysicalMatrixBits.actionEntry P F
      (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F) (diagonalQuery (characteristic P F) p)) =
      (characteristicAccess P a F h).entry (diagonalQuery (characteristic P F) p) := by
  have HS : stage (characteristic P F) p < (characteristic P F).dimension (original p) :=
    ((Berkowitz.QueryBits.select_diagonal_iff _ _ _ _ _).mp ((selector_eq _ _).symm.trans hd)).2.1
  let i : Fin ((characteristic P F).dimension (original p)) := ⟨_, HS⟩
  let r := basisIndex (characteristic P F) basisRowCode p
  let t := basisIndex (characteristic P F) basisColCode p
  exact (actionChild_value P F g (original p) i i r t).trans
    ((characteristicAccess P a F h).entry_eq (original p) i i r t).symm

theorem relative_moment_child (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (c : List Bool) :
    momentValue P F
      (IntegralCriticalFlatBerkowitzQuery.momentWriter P
        (outerPacket (characteristic P F) (IntegralCriticalFlatRelativeFactorBits.packet P c))) =
      (momentFamily (characteristic P F)).value
        (outerPacket (characteristic P F) (IntegralCriticalFlatRelativeFactorBits.packet P c)) := by
  apply moment_child_bounded
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet, basisRowCode,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.mod_lt _ ((characteristic P F).rank_pos c)).le.trans ((by unfold characteristic; exact IntegralMixedPhysicalCaps.rank_cap P F g c))
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet, basisColCode,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.mod_lt _ ((characteristic P F).rank_pos c)).le.trans ((by unfold characteristic; exact IntegralMixedPhysicalCaps.rank_cap P F g c))
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.div_le_self _ _).trans (get_le P .row c)
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.div_le_self _ _).trans (get_le P .col c)

end LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
