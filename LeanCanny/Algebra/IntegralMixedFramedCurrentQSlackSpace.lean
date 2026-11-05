/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQOldHeightSpace
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProducts
public import LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicCoefficients
/-! # Charged current-Q readers for actual marked slack characteristics

Integer leaves stay in their native coefficient sources. Every matrix,
product, power and characteristic coefficient is derived from current-Q
controls, without serialized integer words or a supplied matrix reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQSlackBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedClearedMatrixBits (rank matrix)
open IntegralMixedFramedMatrixValueBits (Matrices)
open IntegralMixedFramedSlackMatrixBits (commonAt sphere regular sphereValue regularValue sphereCoefficient regularCoefficient)
open IntegralMixedFramedSlackCharacteristicBits (spherePolynomial regularPolynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev liftedData (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra

variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) (liftedData P D H))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) (liftedData P D H) c)
include a c hb

theorem cleared_power_evaluator : SpaceFunction (IntegralMixedFramedClearedMatrixPowerBits.powerFamily P D H).value :=
  MatrixPower.ModularAccess.evaluatorWithEntry (IntegralMixedFramedClearedMatrixPowerBits.access P D H)
    (IntegralMixedFramedClearedMatrixPowerBits.controls P a D H)
    ((IntegralMixedFramedClearedMatrixBits.currentQ_evaluator P a D H c hb).precompose
      IntegralMixedFramedClearedMatrixPowerBits.request IntegralMixedFramedClearedMatrixPowerBits.request_FP)

theorem sum_evaluator {N e : List Bool → ℕ} (hN : UnaryFn N) (he : BinaryFn e) : SpaceFunction (IntegralMixedFramedClearedPowerSumBits.value P D H N e) := by
  have EC : BinaryFn (fun q=>N (PaddedIntegralGeneratorSource.base q)) := (BinaryFn.ofUnary hN).comp PaddedIntegralGeneratorSource.base_FP
  have EM := IntegralMixedFramedCompanionQueryBits.callerModulus_binary
  have ES := (cleared_power_evaluator P a D H c hb).precompose
    (IntegralMixedFramedClearedPowerSumBits.request P D H N e) (IntegralMixedFramedClearedPowerSumBits.request_FP P a D H hN he)
  have EE := ModularSum.evaluatorWithModulus ES (fun q=>BinaryNatCode.encode (N (PaddedIntegralGeneratorSource.base q)))
    (fun q=>BinaryNatCode.encode (IntegralMixedFramedCompanionQueryBits.callerModulus q)) EC.bits_mem_FP EM.bits_mem_FP
    IntegralMixedFramedCompanionQueryBits.callerModulus (funext fun _=>Nat.fromBitsLE_bits _)
    (fun q i=>((matrix P D H (PaddedIntegralGeneratorSource.base q) (N (PaddedIntegralGeneratorSource.base q)-i)^e (PaddedIntegralGeneratorSource.base q))
      (IntegralMixedFramedClearedPowerSumBits.row P D H q) (IntegralMixedFramedClearedPowerSumBits.col P D H q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
    (fun q=>by unfold IntegralMixedFramedCompanionQueryBits.callerModulus; omega)
    (fun q i _=>IntegralMixedFramedClearedPowerSumBits.summand_packet P D H N e q i)
  exact EE.congr (funext fun q=>by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedFramedClearedPowerSumBits.value,IntegralMixedFramedClearedPowerSumBits.matrixSum,Matrix.sum_apply,Int.cast_sum])


theorem common_evaluator : SpaceFunction (fun q => residueBits
    (IntegralMixedFramedSlackScalarBits.common P D H q :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
  IntegralMixedFramedCurrentQBankProductBits.common_evaluator P a D H (liftedData P D H) c hb

theorem sphere_space {R : List Bool → ℕ} (hR : BinaryFn R) :
    SpaceFunction (fun q=>residueBits (IntegralMixedFramedSlackScalarBits.sphereDiagonal P D H R q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) := by
  have EQ := IntegralMixedFramedSlackScalarBits.power_evaluator PaddedIntegralGeneratorSource.modulus_FP (BinaryFn.const 2) (common_evaluator P a D H c hb)
  have ED := IntegralMixedFramedSlackScalarBits.dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP (hR.comp PaddedIntegralGeneratorSource.base_FP)
  have ER := IntegralMixedFramedSlackScalarBits.power_evaluator PaddedIntegralGeneratorSource.modulus_FP (BinaryFn.const 2) ED
  have EE := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _
    PaddedIntegralGeneratorSource.modulus_FP EQ ER
  exact EE.congr (funext fun q=>by simp only [IntegralMixedFramedSlackScalarBits.sphereDiagonal,Int.cast_mul,Int.cast_pow,Function.comp_apply])


theorem regularScale_space {d L : List Bool → ℕ} (hd : BinaryFn d) (hL : BinaryFn L) :
    SpaceFunction (fun q=>residueBits (IntegralMixedFramedSlackScalarBits.regularScale P D H d L q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) := by
  have EQ := IntegralMixedFramedSlackScalarBits.power_evaluator PaddedIntegralGeneratorSource.modulus_FP (hd.comp PaddedIntegralGeneratorSource.base_FP)
    (common_evaluator P a D H c hb)
  have EL := IntegralMixedFramedSlackScalarBits.dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP (hL.comp PaddedIntegralGeneratorSource.base_FP)
  have EE := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _
    PaddedIntegralGeneratorSource.modulus_FP EL EQ
  exact EE.congr (funext fun q=>by simp only [IntegralMixedFramedSlackScalarBits.regularScale,Int.cast_mul,Int.cast_pow,Function.comp_apply])


theorem regularDiagonal_space {d L K : List Bool → ℕ} (hd : BinaryFn d) (hL : BinaryFn L) (hK : BinaryFn K) :
    SpaceFunction (fun q=>residueBits (IntegralMixedFramedSlackScalarBits.regularDiagonal P D H d L K q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) := by
  have EL := regularScale_space P a D H c hb hd hL
  have EK := IntegralMixedFramedSlackScalarBits.dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP (hK.comp PaddedIntegralGeneratorSource.base_FP)
  have EP := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _ PaddedIntegralGeneratorSource.modulus_FP EL EK
  have EQ := IntegralMixedFramedSlackScalarBits.power_evaluator PaddedIntegralGeneratorSource.modulus_FP (hd.comp PaddedIntegralGeneratorSource.base_FP)
    (common_evaluator P a D H c hb)
  have EE := ModularResidueSpace.addEvaluator PaddedIntegralGeneratorSource.modulus _ _ PaddedIntegralGeneratorSource.modulus_FP EP EQ
  exact EE.congr (funext fun q=>by simp only [IntegralMixedFramedSlackScalarBits.regularDiagonal,Int.cast_add,Int.cast_mul,Int.cast_pow,Function.comp_apply])



theorem sphere_evaluator {N R : List Bool → ℕ} (hN : UnaryFn N) (hR : BinaryFn R) : SpaceFunction (sphereValue P D H N R) := by
  have EA : SpaceFunction (fun q=>residueBits (sphereCoefficient P D H R (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    sphere_space P a D H c hb hR
  have ED := IntegralMixedFramedMatrixValueBits.diagonal_evaluator P D H a EA
  have ES : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H
      (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N (fun _=>2))) :=
    sum_evaluator P a D H c hb hN (BinaryFn.const 2)
  exact IntegralMixedFramedMatrixValueBits.sub_evaluator P D H ED ES


theorem regular_evaluator {N d R L K : List Bool → ℕ} (hN : UnaryFn N) (hd : BinaryFn d) (hR : BinaryFn R) (hLam : BinaryFn L) (hK : BinaryFn K) :
    SpaceFunction (regularValue P D H N d R L K) := by
  have EA : SpaceFunction (fun q=>residueBits (regularCoefficient P D H d L K (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    regularDiagonal_space P a D H c hb hd hLam hK
  have ED := IntegralMixedFramedMatrixValueBits.diagonal_evaluator P D H a EA
  have ES : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H
      (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N d)) :=
    sum_evaluator P a D H c hb hN hd
  have EL : SpaceFunction (fun q=>residueBits (((2 : ℤ)^L (PaddedIntegralGeneratorSource.base q) : ℤ) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    IntegralMixedFramedSlackScalarBits.dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP
      (hLam.comp PaddedIntegralGeneratorSource.base_FP)
  have ESS := IntegralMixedFramedMatrixValueBits.smul_evaluator P D H (f := fun key=>(2 : ℤ)^L key) EL ES
  have EU : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H (sphere P D H N R)) :=
    sphere_evaluator P a D H c hb hN hR
  have EUP := IntegralMixedFramedMatrixValueBits.power_evaluator P a D H (hd.div (BinaryFn.const 2)) EU
  have EUPS := IntegralMixedFramedMatrixValueBits.smul_evaluator P D H (f := fun key=>(2 : ℤ)^L key) EL EUP
  exact IntegralMixedFramedMatrixValueBits.sub_evaluator P D H
    (IntegralMixedFramedMatrixValueBits.sub_evaluator P D H ED ESS) EUPS


omit a c hb in
private theorem scalar_space (scalar : List Bool → ℤ)
    (ES : SpaceFunction (fun q=>residueBits (scalar (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :
    SpaceFunction (fun z=>residueBits (scalar (RationalSubstitution.IntegerBits.context z) : ZMod (RationalSubstitution.IntegerBits.mValue z))) := by
  have HB (z : List Bool) : PaddedIntegralGeneratorSource.base (IntegralMixedFramedSlackCharacteristicBits.scalarPacket z)=RationalSubstitution.IntegerBits.context z := by
    simp only [IntegralMixedFramedSlackCharacteristicBits.scalarPacket,PaddedIntegralGeneratorSource.base,pairFst_pair]
  have HM (z : List Bool) : IntegralMixedFramedCompanionQueryBits.callerModulus (IntegralMixedFramedSlackCharacteristicBits.scalarPacket z)=RationalSubstitution.IntegerBits.mValue z := by
    simp only [IntegralMixedFramedSlackCharacteristicBits.scalarPacket,IntegralMixedFramedCompanionQueryBits.callerModulus,
      PaddedIntegralGeneratorSource.modulus,RationalSubstitution.IntegerBits.mValue,pairFst_pair,pairSnd_pair]
  exact (ES.precompose IntegralMixedFramedSlackCharacteristicBits.scalarPacket IntegralMixedFramedSlackCharacteristicBits.scalarPacket_FP).congr
    (funext fun z=>congrArg₂ (fun (k : List Bool) (m : ℕ)=>residueBits (scalar k : ZMod m)) (HB z) (HM z))

omit a c hb in
private theorem coefficient_from_entries (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (M : Matrices P D H) (scalar : List Bool → ℤ)
    (EM : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H M))
    (ES : SpaceFunction (fun q=>residueBits (scalar (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :
    SpaceFunction (PrimitivePairBits.coefficient (IntegralMixedFramedSlackCharacteristicBits.polynomial P D H M scalar)) :=
  (IntegralScaledCharacteristicBits.evaluator (IntegralMixedFramedSlackCharacteristicBits.characteristic P D H M) (IntegralMixedFramedSlackCharacteristicBits.access P a D H M)
    (scalar ∘ RationalSubstitution.IntegerBits.context) (fun _=>1) (BinaryFn.const 1)
    (EM.precompose IntegralMixedFramedSlackCharacteristicBits.entryPacket IntegralMixedFramedSlackCharacteristicBits.entryPacket_FP) (scalar_space scalar ES)).congr
      (funext fun z=>IntegralMixedFramedSlackCharacteristicBits.scaled_value P D H M scalar z)


theorem sphere_coefficient_space {N R : List Bool → ℕ} (hN : UnaryFn N) (hR : BinaryFn R) :
    SpaceFunction (PrimitivePairBits.coefficient (spherePolynomial P D H N R)) := by
  have EM : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H (sphere P D H N R)) :=
    sphere_evaluator P a D H c hb hN hR
  have EQ := IntegralMixedFramedSlackScalarBits.power_evaluator PaddedIntegralGeneratorSource.modulus_FP
    (BinaryFn.const 2) (common_evaluator P a D H c hb)
  have ES : SpaceFunction (fun q=>residueBits (((commonAt P D H (PaddedIntegralGeneratorSource.base q)^2 : ℤ) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :=
    EQ.congr (funext fun q=>by
      change residueBits ((IntegralMixedFramedSlackScalarBits.common P D H q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))^2)=
        residueBits (((commonAt P D H (PaddedIntegralGeneratorSource.base q)^2 : ℤ) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
      have HQ : IntegralMixedFramedSlackScalarBits.common P D H q=commonAt P D H (PaddedIntegralGeneratorSource.base q) := rfl
      rw [HQ,Int.cast_pow])

  exact coefficient_from_entries P a D H (sphere P D H N R) (fun key=>commonAt P D H key^2) EM ES


theorem regular_coefficient_space {N d R L K : List Bool → ℕ} (hN : UnaryFn N) (hd : BinaryFn d) (hR : BinaryFn R) (hLam : BinaryFn L) (hK : BinaryFn K) :
    SpaceFunction (PrimitivePairBits.coefficient (regularPolynomial P D H N d R L K)) := by
  have EM : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H (regular P D H N d R L K)) :=
    regular_evaluator P a D H c hb hN hd hR hLam hK
  have ES : SpaceFunction (fun q=>residueBits
      (((2 : ℤ)^L (PaddedIntegralGeneratorSource.base q)*commonAt P D H (PaddedIntegralGeneratorSource.base q)^d (PaddedIntegralGeneratorSource.base q) : ℤ) :
        ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    regularScale_space P a D H c hb hd hLam
  exact coefficient_from_entries P a D H (regular P D H N d R L K)
    (fun key=>(2 : ℤ)^L key*commonAt P D H key^d key) EM ES


end LeanCanny.Algebra.IntegralMixedFramedCurrentQSlackBits
