/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualFactorModel
/-! # Natural matrix selectors for actual monomial factor powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualFactorModel
open LeanCanny.Encoding MatrixPower
open IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false

theorem power_packet_natural (S : IntegralMonomialTermBits.Source) (q : List Bool) (s r t : ℕ) :
    (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family S)).value
      (pair q (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) =
    entryBits (factorPowerMatrix S q s) (r % S.rank q) (t % S.rank q) := by
  generalize hz : pair q (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) = p
  have HQ : pairFst p = q := by rw [← hz, pairFst_pair]
  have HS : Nat.fromBitsLE (IntegralPowerProductBits.factorWord p) = s := by
    rw [← hz, IntegralPowerProductBits.factorWord]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HR : Nat.fromBitsLE (IntegralPowerProductBits.rowWord p) = r := by
    rw [← hz, IntegralPowerProductBits.rowWord]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HT : Nat.fromBitsLE (IntegralPowerProductBits.colWord p) = t := by
    rw [← hz, IntegralPowerProductBits.colWord]
    simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst q
  let := S.ring (pairFst p)
  have HP : 0 < S.rank (pairFst p) := (Nat.zero_le _).trans_lt (S.row (pairFst p)).isLt
  let rr : Fin (S.rank (pairFst p)) := ⟨r % S.rank (pairFst p), Nat.mod_lt _ HP⟩
  let tt : Fin (S.rank (pairFst p)) := ⟨t % S.rank (pairFst p), Nat.mod_lt _ HP⟩
  have HI : IntegralPowerProductBits.oldIndex (IntegralMonomialTermBits.family S) IntegralPowerProductBits.rowWord p = rr := by
    apply Fin.ext
    change Nat.fromBitsLE (IntegralPowerProductBits.rowWord p) % S.rank (pairFst p) = r % S.rank (pairFst p)
    rw [HR]
  have HJ : IntegralPowerProductBits.oldIndex (IntegralMonomialTermBits.family S) IntegralPowerProductBits.colWord p = tt := by
    apply Fin.ext
    change Nat.fromBitsLE (IntegralPowerProductBits.colWord p) % S.rank (pairFst p) = t % S.rank (pairFst p)
    rw [HT]
  rw [ModularFamily.value]
  let T := Algebra.leftMulMatrix (S.basis (pairFst p))
    (IntegralMonomialTermBits.factor S (pairFst p) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p)))
  change residueBits ((T.map (Int.castRingHom (ZMod (S.modulus (pairFst p)))) ^
    IntegralMonomialTermBits.factorExponent S (pairFst p) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p)))
      (IntegralPowerProductBits.oldIndex (IntegralMonomialTermBits.family S) IntegralPowerProductBits.rowWord p)
      (IntegralPowerProductBits.oldIndex (IntegralMonomialTermBits.family S) IntegralPowerProductBits.colWord p)) = _
  rw [← Matrix.map_pow, Matrix.map_apply]
  dsimp only [T]
  rw [← map_pow, HS, HI, HJ]
  exact (entryBits_fin (factorPowerMatrix S (pairFst p) s) rr tt).symm

end LeanCanny.Algebra.IntegralCriticalActualFactorModel
