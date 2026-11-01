/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralReductionActionCorrect
/-! # Freezing one actual shifted-action source before scalar evaluation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionActionFreezeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralReductionActionBits
set_option backward.isDefEq.respectTransparency false

noncomputable def freeze (S : Source) (c : List Bool) : Source where
  dimension _ := S.dimension c
  rank _ := S.rank c
  carrier _ := S.carrier c
  ring _ := S.ring c
  nontrivial _ := S.nontrivial c
  basis _ := S.basis c
  matrix _ := S.matrix c
  modulus _ := S.modulus c
  modulus_ne_zero _ := S.modulus_ne_zero c
  coefficient _ := S.coefficient c
  basisRow _ := S.basisRow c
  basisCol _ := S.basisCol c
  dimension_pos _ := S.dimension_pos c
  normal _ := S.normal c
  shift _ := S.shift c
  bound _ := S.bound c

noncomputable def atPower (S : Source) (r t : ℕ) : List Bool :=
  (powerFamily S).value
    (pair (IntegralBlockMomentBits.context [] (r % S.rank []) (t % S.rank []))
      (pair (BinaryNatCode.encode (r / S.rank [])) (BinaryNatCode.encode (t / S.rank []))))

theorem value_freeze_point (S : Source) (p : List Bool) :
    (powerFamily S).value p = (powerFamily (freeze S (IntegralBerkowitzBlockBits.original p))).value p := rfl

theorem value_freeze (S : Source) (c : List Bool) (r t : ℕ) :
    (powerFamily S).value
      (pair (IntegralBlockMomentBits.context c (r % S.rank c) (t % S.rank c))
        (pair (BinaryNatCode.encode (r / S.rank c)) (BinaryNatCode.encode (t / S.rank c)))) =
      atPower (freeze S c) r t := by
  have H := value_freeze_point S
    (pair (IntegralBlockMomentBits.context c (r % S.rank c) (t % S.rank c))
      (pair (BinaryNatCode.encode (r / S.rank c)) (BinaryNatCode.encode (t / S.rank c))))
  have HO : IntegralBerkowitzBlockBits.original
      (pair (IntegralBlockMomentBits.context c (r % S.rank c) (t % S.rank c))
        (pair (BinaryNatCode.encode (r / S.rank c)) (BinaryNatCode.encode (t / S.rank c)))) = c := by
    simp only [IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, pairFst_pair]
  rw [HO] at H
  rw [H]
  unfold atPower powerFamily IntegralBlockPowerBits.Family.value
  simp only [freeze, outerIndex, IntegralBerkowitzBlockBits.basisIndex, IntegralBerkowitzBlockBits.basisRowCode,
    IntegralBerkowitzBlockBits.basisColCode, IntegralBlockMomentBits.context,
    MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.IntegralReductionActionFreezeBits
