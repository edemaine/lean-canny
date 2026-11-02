/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightReferenceSum
/-! # Native bank powers and charged original scale cofactors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightScaleFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open IntegralMixedFramedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus BinaryNat.powMod

noncomputable def power (P : Parameters) (z : List Bool) :=
  BinaryNat.powMod (pair (IntegralMixedFramedHeightBankProductBits.value P z)
    (pair (BinaryNatCode.encode (P.ambient (RankedHistoryTask.root (pairFst z))))
      (BinaryNatCode.encode (modulus P (pairFst z) - 1))))

theorem power_FP (P : Parameters) (a : Access P) : power P ∈ FP := by
  have HA : BinaryFn (fun z => P.ambient (RankedHistoryTask.root (pairFst z))) :=
    (BinaryFn.ofUnary (a.ambient.comp RankedHistoryTask.root_FP)).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z) - 1) := ((modulus_binary P a).sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair (IntegralMixedFramedHeightBankProductBits.value_FP P a) (mem_FP_pair HA.bits_mem_FP HM.bits_mem_FP))
    BinaryNat.powMod_mem_FP

noncomputable def powerScalar (P : Parameters) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  (∏ i ∈ Finset.range (birth P (pairFst z)), IntegralMixedFramedHeightBankProductBits.scalar P z i) ^
    P.ambient (RankedHistoryTask.root (pairFst z))

theorem power_value (P : Parameters) (z : List Bool) : power P z = residueBits (powerScalar P z) := by
  unfold power IntegralMixedFramedHeightBankProductBits.value
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (modulus_ne_zero P (pairFst z)) _

noncomputable def factor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  multiply P (pair z (pair (power P z) (IntegralMixedFramedHeightCellAccessBits.scaleProduct P D J z)))

attribute [local irreducible] power multiply IntegralMixedFramedHeightCellAccessBits.scaleProduct

theorem factor_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (factor P D J) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((SpaceFunction.ofFP _ (power_FP P a)).pairOutputs
    (IntegralMixedFramedHeightCellAccessBits.scaleProduct_space P a D J hp))).postcompose (multiply P) (multiply_FP P a)

noncomputable def factorScalar (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  powerScalar P z * (∏ i ∈ Finset.range (IntegralMixedFramedHeightCellAccessBits.arity P z), IntegralMixedFramedHeightCellAccessBits.scaleScalar P D J z i)

theorem factor_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :
    factor P D J z = residueBits (factorScalar P D J z) := by
  rw [factor, power_value, IntegralMixedFramedHeightCellAccessBits.scaleProduct, multiply_packet]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedHeightScaleFactorBits
