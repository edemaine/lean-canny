/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficient
/-! # Literal WordList coordinate packets for the actual radial eliminant

The coordinate selector occupies table entry zero. A bare binary coordinate
word is not that table; this writer emits the actual decoder's representation.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open FormulaSignSlotCenteredRadialGraph
set_option backward.isDefEq.respectTransparency false

def packet (c : List Bool) (i : ℕ) := pair c (WordList.encode [BinaryNatCode.encode i])
def writer (q : List Bool) := pair (pairFst q) (WordList.encode [BinaryNat.normalize (pairSnd q)])
theorem writer_FP : writer ∈ FP := by
  unfold writer WordList.encode
  exact mem_FP_pair pairFst_mem_FP
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (constFn_mem_FP []))
theorem writer_packet (c : List Bool) (i : ℕ) : writer (pair c (BinaryNatCode.encode i)) = packet c i := by
  simp only [writer, packet, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
theorem root (c : List Bool) (i : ℕ) : pairFst (packet c i) = c := by rw [packet, pairFst_pair]
theorem selected (c : List Bool) (i : ℕ) :
    (FormulaSignSlotRadialEliminantInput.coordinate (packet c i)).val = min i (N c + d c) := by
  dsimp only [FormulaSignSlotRadialEliminantInput.coordinate]
  simp only [FormulaSignSlotRadialEliminantInput.field, FormulaSignSlotRadialEliminantInput.spatialCount,
    FormulaSignSlotRadialFormalInput.spatial, packet, pairFst_pair, pairSnd_pair, WordList.get_encode,
    List.getElem?_cons_zero, Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.add_sub_cancel_right]

private theorem eliminant_heq (q c : List Bool) (hc : pairFst q = c)
    (i : Fin (N c + d c + 1)) (hi : (FormulaSignSlotRadialEliminantInput.coordinate q).val = i.val) :
    HEq (FormulaSignSlotRadialFormalEliminant.eliminant (pairFst q)
      (FormulaSignSlotRadialEliminantInput.coordinate q)) (FormulaSignSlotRadialFormalEliminant.eliminant c i) := by
  cases hc
  have HI : FormulaSignSlotRadialEliminantInput.coordinate q = i := Fin.ext hi
  rw [HI]

theorem actual_eliminant (c : List Bool) (i : Fin (N c + d c + 1)) :
    HEq (FormulaSignSlotRadialFormalEliminant.eliminant (pairFst (packet c i.val))
      (FormulaSignSlotRadialEliminantInput.coordinate (packet c i.val)))
        (FormulaSignSlotRadialFormalEliminant.eliminant c i) := by
  apply eliminant_heq (packet c i.val) c (root c i.val) i
  rw [selected, Nat.min_eq_left (by omega)]

end LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
