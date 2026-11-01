/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightReferenceSum
/-! # Native bank powers and charged original scale cofactors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightScaleFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightCellsBits (cell Primitive)
open IntegralMixedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus BinaryNat.powMod

noncomputable def power (P : Parameters) (z : List Bool) :=
  BinaryNat.powMod (pair (IntegralMixedHeightBankProductBits.value P z)
    (pair (BinaryNatCode.encode (P.ambient (RankedHistoryTask.root (pairFst z))))
      (BinaryNatCode.encode (modulus P (pairFst z) - 1))))

theorem power_FP (P : Parameters) (a : Access P) : power P ∈ FP := by
  have HA : BinaryFn (fun z => P.ambient (RankedHistoryTask.root (pairFst z))) :=
    (BinaryFn.ofUnary (a.ambient.comp RankedHistoryTask.root_FP)).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z) - 1) := ((modulus_binary P a).sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair (IntegralMixedHeightBankProductBits.value_FP P a) (mem_FP_pair HA.bits_mem_FP HM.bits_mem_FP))
    BinaryNat.powMod_mem_FP

noncomputable def powerScalar (P : Parameters) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  (∏ i ∈ Finset.range (birth P (pairFst z)), IntegralMixedHeightBankProductBits.scalar P z i) ^
    P.ambient (RankedHistoryTask.root (pairFst z))

theorem power_value (P : Parameters) (z : List Bool) : power P z = residueBits (powerScalar P z) := by
  unfold power IntegralMixedHeightBankProductBits.value
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (modulus_ne_zero P (pairFst z)) _

noncomputable def factor (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :=
  multiply P (pair z (pair (power P z) (IntegralMixedHeightCellAccessBits.scaleProduct P D z)))

theorem factor_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) :
    SpaceFunction (factor P D) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((SpaceFunction.ofFP _ (power_FP P a)).pairOutputs
    (IntegralMixedHeightCellAccessBits.scaleProduct_space P a D hp))).postcompose (multiply P) (multiply_FP P a)

noncomputable def factorScalar (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  powerScalar P z * (∏ i ∈ Finset.range (IntegralMixedHeightCellAccessBits.arity P z), IntegralMixedHeightCellAccessBits.scaleScalar P D z i)

theorem factor_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :
    factor P D z = residueBits (factorScalar P D z) := by
  rw [factor, power_value, IntegralMixedHeightCellAccessBits.scaleProduct, multiply_packet]
  rfl

end LeanCanny.Algebra.IntegralMixedHeightScaleFactorBits
