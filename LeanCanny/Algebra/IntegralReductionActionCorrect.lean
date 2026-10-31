/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralReductionActionSource

/-! # Native shifted reduction entries agree with the actual action matrix -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (c : List Bool) (i j r t : ℕ) : List Bool :=
  pair (IntegralBlockMomentBits.context c r t) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))

theorem original_packet (c : List Bool) (i j r t : ℕ) : original (packet c i j r t) = c := by
  simp only [packet, original, IntegralBlockMomentBits.context, pairFst_pair]

theorem outerIndex_packet (S : Source) (c : List Bool) (i j : Fin (S.dimension c)) (r t : ℕ) :
    (outerIndex S MatrixMoment.EntryBits.rowIndex (packet c i.val j.val r t)).val = i.val ∧
    (outerIndex S MatrixMoment.EntryBits.colIndex (packet c i.val j.val r t)).val = j.val := by
  simp only [outerIndex, packet, original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
    MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt,
    and_self]

theorem power_packet (S : Source) (c : List Bool) (i j : Fin (S.dimension c)) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (powerFamily S).value (packet c i.val j.val r.val t.val) =
      residueBits ((Algebra.leftMulMatrix (S.basis c)
        ((S.matrix c ^ (S.bound c + 1)) i (S.shift c j)) r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  generalize hz : packet c i.val j.val r.val t.val = p
  have ho : original p = c := by rw [← hz, original_packet]
  have hi : (outerIndex S MatrixMoment.EntryBits.rowIndex p).val = i.val := by
    rw [← hz]
    exact (outerIndex_packet S c i j r.val t.val).1
  have hj : (outerIndex S MatrixMoment.EntryBits.colIndex p).val = j.val := by
    rw [← hz]
    exact (outerIndex_packet S c i j r.val t.val).2
  have hr : (IntegralBerkowitzBlockBits.basisIndex S.toSource basisRowCode p).val = r.val := by
    change Nat.fromBitsLE (basisRowCode p) % S.rank (original p) = r.val
    rw [← hz]
    simp only [packet, basisRowCode, original, IntegralBlockMomentBits.context,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt r.isLt]
  have ht : (IntegralBerkowitzBlockBits.basisIndex S.toSource basisColCode p).val = t.val := by
    change Nat.fromBitsLE (basisColCode p) % S.rank (original p) = t.val
    rw [← hz]
    simp only [packet, basisColCode, original, IntegralBlockMomentBits.context,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt t.isLt]
  subst c
  have HI : outerIndex S MatrixMoment.EntryBits.rowIndex p = i := Fin.ext hi
  have HJ : outerIndex S MatrixMoment.EntryBits.colIndex p = j := Fin.ext hj
  have HR : IntegralBerkowitzBlockBits.basisIndex S.toSource basisRowCode p = r := Fin.ext hr
  have HT : IntegralBerkowitzBlockBits.basisIndex S.toSource basisColCode p = t := Fin.ext ht
  change residueBits ((Algebra.leftMulMatrix (S.basis (original p))
    ((S.matrix (original p) ^ (S.bound (original p) + 1))
      (outerIndex S MatrixMoment.EntryBits.rowIndex p)
      (S.shift (original p) (outerIndex S MatrixMoment.EntryBits.colIndex p)))
    (IntegralBerkowitzBlockBits.basisIndex S.toSource basisRowCode p)
    (IntegralBerkowitzBlockBits.basisIndex S.toSource basisColCode p) : ℤ) : ZMod (S.modulus (original p))) = _
  rw [HI, HJ, HR, HT]

noncomputable def entryProgram (S : Source) (p : List Bool) : List Bool :=
  if normalGuard S p then (powerFamily S).value p else []

noncomputable def Source.actionMatrix (S : Source) (c : List Bool) :
    Matrix (Fin (S.dimension c)) (Fin (S.dimension c)) (S.carrier c) := by
  letI := S.ring c
  exact GradedReductionAnnihilator.paddedMatrix (S.matrix c) (S.normal c) (S.bound c) (S.shift c)

noncomputable def actionSource (S : Source) : IntegralBerkowitzBlockBits.Source :=
  { S.toSource with matrix := S.actionMatrix }

theorem entry_correct (S : Source) (c : List Bool) (i j : Fin (S.dimension c)) (r t : Fin (S.rank c)) :
    entryProgram S (packet c i.val j.val r.val t.val) =
      residueBits (((actionSource S).entryMatrix c i j r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  have HG : normalGuard S (packet c i.val j.val r.val t.val) ↔ S.normal c j := by
    generalize hz : packet c i.val j.val r.val t.val = p
    have ho : original p = c := by rw [← hz, original_packet]
    have hj : (outerIndex S MatrixMoment.EntryBits.colIndex p).val = j.val := by
      rw [← hz]
      exact (outerIndex_packet S c i j r.val t.val).2
    subst c
    have HJ : outerIndex S MatrixMoment.EntryBits.colIndex p = j := Fin.ext hj
    unfold normalGuard
    rw [HJ]
  change entryProgram S _ = residueBits ((Algebra.leftMulMatrix (S.basis c)
    (if S.normal c j then (S.matrix c ^ (S.bound c + 1)) i (S.shift c j) else 0) r t : ℤ) : ZMod (S.modulus c))
  rw [entryProgram]
  by_cases hn : S.normal c j
  · rw [ite_eq_left (HG.mpr hn), ite_eq_left hn, power_packet]
  · rw [ite_eq_right (fun h => hn (HG.mp h)), ite_eq_right hn]
    simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero,
      BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.IntegralReductionActionBits
