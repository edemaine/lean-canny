/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockSpace
public import LeanCanny.Algebra.ScaledGradedReductionAnnihilator
public import LeanCanny.Algebra.ModularPowFP

/-! # Native multiplication matrices of scalar-rescaled characteristic coefficients

Substitution by c^e*X multiplies coefficient k by c^(e*k). The integer
scalar is evaluated modulo the same caller modulus, then powered and
multiplied natively. Both original reader costs are charged, including
when c has no polynomial-time signed integer output.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScaledCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem pow_residue (m e : ℕ) (hm : m ≠ 0) (x : ZMod m) :
    BinaryNat.powMod (pair (residueBits x)
      (pair (BinaryNatCode.encode e) (BinaryNatCode.encode (m - 1)))) = residueBits (x ^ e) := by
  let : NeZero m := ⟨hm⟩
  have hx : ((x.val ^ e : ℕ) : ZMod m) = x ^ e := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [← hx]
  simp only [BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair,
    residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_natCast]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]

noncomputable def value (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((ScaledGradedReductionAnnihilator.polynomial (S.matrix c) (scalar c : S.carrier c) (exponent c)).coeff
      (S.coefficient c)) (S.basisRow c) (S.basisCol c) : ℤ) : ZMod (S.modulus c))

theorem value_eq (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (c : List Bool) :
    value S scalar exponent c = residueBits
      (((S.coefficientMatrix c (S.coefficient c) (S.basisRow c) (S.basisCol c) : ℤ) : ZMod (S.modulus c)) *
        (scalar c : ZMod (S.modulus c)) ^ (exponent c * S.coefficient c)) := by
  let := S.ring c
  have HC : (S.matrix c).charpoly.coeff (S.coefficient c) *
      (scalar c : S.carrier c) ^ (exponent c * S.coefficient c) =
      (scalar c ^ (exponent c * S.coefficient c)) • (S.matrix c).charpoly.coeff (S.coefficient c) := by
    rw [zsmul_eq_mul, Int.cast_pow, mul_comm]
  unfold value
  rw [ScaledGradedReductionAnnihilator.coefficient, HC, map_zsmul, Matrix.smul_apply, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, mul_comm]
  simp only [Int.cast_id, Int.cast_pow, IntegralBerkowitzBlockBits.Source.coefficientMatrix]

def powerPost (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ) (z : List Bool) : List Bool :=
  BinaryNat.powMod (pair (pairSnd z)
    (pair (BinaryNatCode.encode (exponent (pairFst z) * S.coefficient (pairFst z)))
      (BinaryNatCode.encode (S.modulus (pairFst z) - 1))))

theorem powerPost_FP (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S)
    (exponent : List Bool → ℕ) (he : BinaryFn exponent) : powerPost S exponent ∈ FP := by
  have HE : BinaryFn (fun z => exponent (pairFst z) * S.coefficient (pairFst z)) :=
    (he.mul a.coefficient).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => S.modulus (pairFst z) - 1) :=
    (a.modulus.sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_pair HE.bits_mem_FP HM.bits_mem_FP)) BinaryNat.powMod_mem_FP

theorem powerPost_packet (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ)
    (c : List Bool) (x : ZMod (S.modulus c)) :
    powerPost S exponent (pair c (residueBits x)) = residueBits (x ^ (exponent c * S.coefficient c)) := by
  simp only [powerPost, pairFst_pair, pairSnd_pair]
  exact pow_residue _ _ (S.modulus_ne_zero c) x

def multiplyPost (S : IntegralBerkowitzBlockBits.Source) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (S.modulus (pairFst z))) (pairSnd z))

theorem multiplyPost_FP (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S) :
    multiplyPost S ∈ FP := by
  have HM : BinaryFn (fun z => S.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

theorem multiplyPost_packet (S : IntegralBerkowitzBlockBits.Source) (c : List Bool) (x y : ZMod (S.modulus c)) :
    multiplyPost S (pair c (pair (residueBits x) (residueBits y))) = residueBits (x * y) := by
  simp only [multiplyPost, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ x y

attribute [local irreducible] value powerPost multiplyPost IntegralBerkowitzBlockBits.Source.value

theorem evaluator (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S)
    (scalar : List Bool → ℤ) (exponent : List Bool → ℕ) (he : BinaryFn exponent)
    (E : SpaceFunction a.entry)
    (EC : SpaceFunction (fun c => residueBits (scalar c : ZMod (S.modulus c)))) :
    SpaceFunction (value S scalar exponent) := by
  have EP := EC.withInput.postcompose (powerPost S exponent) (powerPost_FP S a exponent he)
  have EQ := IntegralBerkowitzBlockBits.evaluator S a E
  refine ((EQ.pairOutputs EP).withInput.postcompose (multiplyPost S) (multiplyPost_FP S a)).congr ?_
  funext c
  change multiplyPost S (pair c (pair (S.value c)
    (powerPost S exponent (pair c (residueBits (scalar c : ZMod (S.modulus c))))))) = _
  rw [powerPost_packet, IntegralBerkowitzBlockBits.Source.value, multiplyPost_packet]
  exact (value_eq S scalar exponent c).symm

end LeanCanny.Algebra.IntegralScaledCharacteristicBits
