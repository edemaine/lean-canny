/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedMatrixValueSpace
/-! # Matrix powers preserve the same actual bank and caller modulus

This composition lemma charges its entry program. The concrete slack
constructors instantiate that program using actual old-height arithmetic.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedMatrixValueBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (rank)
open IntegralMixedFramedClearedPowerSumBits (row col)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private noncomputable def powerFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) (e : List Bool → ℕ) : MatrixPower.ModularFamily where
  dimension q := rank P D H (PaddedIntegralGeneratorSource.base q)
  modulus := IntegralMixedFramedCompanionQueryBits.callerModulus
  exponent q := e (PaddedIntegralGeneratorSource.base q)
  row := row P D H
  col := col P D H
  matrix q := (M (PaddedIntegralGeneratorSource.base q)).map (Int.castRingHom (ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
  modulus_ne_zero q := by unfold IntegralMixedFramedCompanionQueryBits.callerModulus; omega

private def request (z : List Bool) :=
  pair (pair (PaddedIntegralGeneratorSource.base (pairFst z)) (PaddedIntegralGeneratorSource.modulus (pairFst z))) (pairSnd z)

private theorem request_FP : request∈FP :=
  mem_FP_pair (mem_FP_pair
    (mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.base) pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP)
    (mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.modulus) pairFst_mem_FP PaddedIntegralGeneratorSource.modulus_FP)) pairSnd_mem_FP

private noncomputable def powerAccess (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) (e : List Bool → ℕ) : ModularAccess (powerFamily P D H M e) where
  dimension q := BinaryNatCode.encode ((powerFamily P D H M e).dimension q)
  modulus q := BinaryNatCode.encode ((powerFamily P D H M e).modulus q)
  exponent q := BinaryNatCode.encode ((powerFamily P D H M e).exponent q)
  row q := BinaryNatCode.encode ((powerFamily P D H M e).row q).val
  col q := BinaryNatCode.encode ((powerFamily P D H M e).col q).val
  entry := value P D H M ∘ request
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq q r t := by
    have HP : request (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
        pair (pair (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q))
          (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)) := by
      simp only [request,pairFst_pair,pairSnd_pair]
    rw [Function.comp_apply,HP]
    exact value_packet P D H M (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q) r t

private theorem power_controls (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) {e : List Bool → ℕ} (he : BinaryFn e) : (powerAccess P D H M e).ControlsPolyTime := by
  have HD : BinaryFn (powerFamily P D H M e).dimension :=
    (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H).comp PaddedIntegralGeneratorSource.base_FP
  have HE : BinaryFn (powerFamily P D H M e).exponent := he.comp PaddedIntegralGeneratorSource.base_FP
  exact ⟨HD.bits_mem_FP,IntegralMixedFramedCompanionQueryBits.callerModulus_binary.bits_mem_FP,HE.bits_mem_FP,
    (IntegralMixedFramedClearedPowerSumBits.row_binary P a D H).bits_mem_FP,
    (IntegralMixedFramedClearedPowerSumBits.col_binary P a D H).bits_mem_FP⟩

private theorem power_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) (e : List Bool → ℕ) (q : List Bool) :
    (powerFamily P D H M e).value q=value P D H (fun key=>M key^e key) q := by
  change residueBits (((M (PaddedIntegralGeneratorSource.base q)).map
    (Int.castRingHom (ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))^e (PaddedIntegralGeneratorSource.base q))
      (row P D H q) (col P D H q))=_
  rw [←Matrix.map_pow,Matrix.map_apply]
  rfl

theorem power_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {M : Matrices P D H} {e : List Bool → ℕ} (he : BinaryFn e) (EM : SpaceFunction (value P D H M)) :
    SpaceFunction (value P D H (fun key=>M key^e key)) :=
  (ModularAccess.evaluatorWithEntry (powerAccess P D H M e) (power_controls P a D H M he)
    (EM.precompose request request_FP)).congr (funext fun q=>power_value P D H M e q)

end LeanCanny.Algebra.IntegralMixedFramedMatrixValueBits
