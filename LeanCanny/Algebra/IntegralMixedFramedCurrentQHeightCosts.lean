/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeHeightActual
/-! # Original affine and scale costs exclude the current-bank slope

Only tags zero through two are original cells. The slope is restored from
already charged earlier-producer replies by a separate postprocessor.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
structure LowControls (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) : Prop where
  read : ∀ tag, tag<3 → SpaceFunction (IntegralMixedFramedHeightCellAccessBits.read P D J tag)
end LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
namespace LeanCanny.Algebra.IntegralMixedFramedHeightCellAccessBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus IntegralMixedFramedScalarCellsBits.reader

open IntegralMixedFramedCurrentQHeightBits (LowControls)

theorem scaleTerm_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (scaleTerm P D J) := by
  have HQ := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HI : BinaryFn (fun p => get P .slot8 (pairFst (pairFst p))) := (get_binary P a .slot8).comp HQ
  have HM : BinaryFn (fun p => modulus P (pairFst (pairFst p))) := (modulus_binary P a).comp HQ
  have E := SpaceFunction.branch _ ((BinaryFn.fromBits pairSnd_mem_FP).eq HI).flag_mem_FP
    (SpaceFunction.ofFP _ (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)) (hp.read 2 (by decide))
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)


theorem scaleProduct_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (scaleProduct P D J) := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have E := ModularProduct.evaluatorWithModulus (scaleTerm_space_low P a D J hp)
    (fun z => BinaryNatCode.encode (arity P z)) (fun z => BinaryNatCode.encode (modulus P (pairFst z)))
    (BinaryFn.ofUnary (arity_unary P a)).bits_mem_FP HM.bits_mem_FP
    (fun z => modulus P (pairFst z)) (funext fun _ => Nat.fromBitsLE_bits _) (scaleScalar P D J)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z))) (fun z i _ => scaleTerm_packet P D J z i)
  exact E.congr (funext fun z => by simp only [scaleProduct, BinaryNatCode.encode, Nat.fromBitsLE_bits])


end LeanCanny.Algebra.IntegralMixedFramedHeightCellAccessBits

namespace LeanCanny.Algebra.IntegralMixedFramedHeightReferenceSumBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus BinaryNat.mulMod BinaryNat.mod

open IntegralMixedFramedCurrentQHeightBits (LowControls)

theorem term_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (term P D J) :=
  ((SpaceFunction.ofFP _ pairFst_mem_FP).pairOutputs ((hp.read 1 (by decide)).pairOutputs
    (SpaceFunction.ofFP _ (heightRead_FP P a)))).postcompose (multiply P) (multiply_FP P a)


theorem value_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (value P D J) := by
  have HC : BinaryFn (fun z => birth P (pairFst z)) := (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have E := ModularSum.evaluatorWithModulus (term_space_low P a D J hp) (fun z => BinaryNatCode.encode (birth P (pairFst z)))
    (fun z => BinaryNatCode.encode (modulus P (pairFst z))) HC.bits_mem_FP HM.bits_mem_FP
    (fun z => modulus P (pairFst z)) (funext fun _ => Nat.fromBitsLE_bits _) (scalar P D J)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z))) (fun z i _ => term_packet P D J z i)
  exact E.congr (funext fun z => by simp only [value, BinaryNatCode.encode, Nat.fromBitsLE_bits])


end LeanCanny.Algebra.IntegralMixedFramedHeightReferenceSumBits

namespace LeanCanny.Algebra.IntegralMixedFramedHeightAffineSumBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus ArithmeticBits.combine

open IntegralMixedFramedCurrentQHeightBits (LowControls)

theorem coefficient_zero_space (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (coefficient P D J 0) :=
  (hp.read 0 (by decide)).precompose (fun z => pair z (BinaryNatCode.encode 0))
    (mem_FP_pair id_mem_FP (constFn_mem_FP _))

theorem diagonalConstant_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (diagonalConstant P D J) := by
  have E := SpaceFunction.branch _ (diagonal_FP P a).flag_mem_FP (coefficient_zero_space P D J hp) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)


theorem value_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (value P D J) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedFramedHeightReferenceSumBits.value_space_low P a D J hp).pairOutputs
    ((SpaceFunction.ofFP _ (IntegralMixedFramedHeightBankProductBits.value_FP P a)).pairOutputs (diagonalConstant_space_low P a D J hp)))).postcompose (finish P) (finish_FP P a)


end LeanCanny.Algebra.IntegralMixedFramedHeightAffineSumBits

namespace LeanCanny.Algebra.IntegralMixedFramedHeightScaleFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open IntegralMixedFramedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus BinaryNat.powMod

open IntegralMixedFramedCurrentQHeightBits (LowControls)

attribute [local irreducible] power multiply factor IntegralMixedFramedHeightCellAccessBits.scaleProduct

theorem factor_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (factor P D J) := by
  have E := ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((SpaceFunction.ofFP _ (power_FP P a)).pairOutputs
    (IntegralMixedFramedHeightCellAccessBits.scaleProduct_space_low P a D J hp))).postcompose (multiply P) (multiply_FP P a)
  exact E.congr (funext fun z => by unfold factor; rfl)


end LeanCanny.Algebra.IntegralMixedFramedHeightScaleFactorBits

namespace LeanCanny.Algebra.IntegralMixedFramedHeightPostBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open IntegralMixedFramedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus

open IntegralMixedFramedCurrentQHeightBits (LowControls)

attribute [local irreducible] constantValue multiply IntegralMixedFramedHeightScaleFactorBits.factor IntegralMixedFramedHeightAffineSumBits.value

theorem constantValue_space_low (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : LowControls P D J) :
    SpaceFunction (constantValue P D J) := by
  have E := ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedFramedHeightScaleFactorBits.factor_space_low P a D J hp).pairOutputs
    (IntegralMixedFramedHeightAffineSumBits.value_space_low P a D J hp))).postcompose (multiply P) (multiply_FP P a)
  exact E.congr (funext fun z => by unfold constantValue; rfl)


end LeanCanny.Algebra.IntegralMixedFramedHeightPostBits
