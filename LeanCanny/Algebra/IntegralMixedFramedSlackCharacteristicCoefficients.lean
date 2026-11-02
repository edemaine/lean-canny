/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicSpace
/-! # Actual U/V characteristic coefficients charge only original inputs -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedMatrixValueBits (Matrices)
open IntegralMixedFramedSlackMatrixBits (commonAt sphere regular)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedHistory.commonDenominator IntegralMixedFramedHistoryFamilyBits.family

private theorem scalar_space (scalar : List Bool → ℤ)
    (ES : SpaceFunction (fun q=>residueBits (scalar (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :
    SpaceFunction (fun z=>residueBits (scalar (RationalSubstitution.IntegerBits.context z) : ZMod (RationalSubstitution.IntegerBits.mValue z))) := by
  have HB (z : List Bool) : PaddedIntegralGeneratorSource.base (scalarPacket z)=RationalSubstitution.IntegerBits.context z := by
    simp only [scalarPacket,PaddedIntegralGeneratorSource.base,pairFst_pair]
  have HM (z : List Bool) : IntegralMixedFramedCompanionQueryBits.callerModulus (scalarPacket z)=RationalSubstitution.IntegerBits.mValue z := by
    simp only [scalarPacket,IntegralMixedFramedCompanionQueryBits.callerModulus,
      PaddedIntegralGeneratorSource.modulus,RationalSubstitution.IntegerBits.mValue,pairFst_pair,pairSnd_pair]
  exact (ES.precompose scalarPacket scalarPacket_FP).congr
    (funext fun z=>congrArg₂ (fun (k : List Bool) (m : ℕ)=>residueBits (scalar k : ZMod m)) (HB z) (HM z))

private theorem coefficient_from_entries (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (M : Matrices P D H) (scalar : List Bool → ℤ)
    (EM : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H M))
    (ES : SpaceFunction (fun q=>residueBits (scalar (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial P D H M scalar)) :=
  (IntegralScaledCharacteristicBits.evaluator (characteristic P D H M) (access P a D H M)
    (scalar ∘ RationalSubstitution.IntegerBits.context) (fun _=>1) (BinaryFn.const 1)
    (EM.precompose entryPacket entryPacket_FP) (scalar_space scalar ES)).congr
      (funext fun z=>scaled_value P D H M scalar z)

noncomputable def spherePolynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N R : List Bool → ℕ) := polynomial P D H (sphere P D H N R) (fun key=>commonAt P D H key^2)
noncomputable def regularPolynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N d R L K : List Bool → ℕ) := polynomial P D H (regular P D H N d R L K)
      (fun key=>(2 : ℤ)^L key*commonAt P D H key^d key)

theorem sphere_coefficient_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {N R : List Bool → ℕ} (hN : UnaryFn N) (hR : BinaryFn R) :
    SpaceFunction (PrimitivePairBits.coefficient (spherePolynomial P D H N R)) := by
  have EM : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H (sphere P D H N R)) :=
    IntegralMixedFramedSlackMatrixBits.sphere_evaluator P a D H s hs hF hL hN hR
  have EQ := IntegralMixedFramedSlackScalarBits.power_evaluator PaddedIntegralGeneratorSource.modulus_FP
    (BinaryFn.const 2) (IntegralMixedFramedSlackScalarBits.common_space P a D H s hs hF hL)
  have ES : SpaceFunction (fun q=>residueBits (((commonAt P D H (PaddedIntegralGeneratorSource.base q)^2 : ℤ) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :=
    EQ.congr (funext fun q=>by
      change residueBits ((IntegralMixedFramedSlackScalarBits.common P D H q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))^2)=
        residueBits (((commonAt P D H (PaddedIntegralGeneratorSource.base q)^2 : ℤ) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
      have HQ : IntegralMixedFramedSlackScalarBits.common P D H q=commonAt P D H (PaddedIntegralGeneratorSource.base q) := rfl
      rw [HQ,Int.cast_pow])

  exact coefficient_from_entries P a D H (sphere P D H N R) (fun key=>commonAt P D H key^2) EM ES

theorem regular_coefficient_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {N d R L K : List Bool → ℕ} (hN : UnaryFn N) (hd : BinaryFn d) (hR : BinaryFn R) (hLam : BinaryFn L) (hK : BinaryFn K) :
    SpaceFunction (PrimitivePairBits.coefficient (regularPolynomial P D H N d R L K)) := by
  have EM : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H (regular P D H N d R L K)) :=
    IntegralMixedFramedSlackMatrixBits.regular_evaluator P a D H s hs hF hL hN hd hR hLam hK
  have ES : SpaceFunction (fun q=>residueBits
      (((2 : ℤ)^L (PaddedIntegralGeneratorSource.base q)*commonAt P D H (PaddedIntegralGeneratorSource.base q)^d (PaddedIntegralGeneratorSource.base q) : ℤ) :
        ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    IntegralMixedFramedSlackScalarBits.regularScale_space P a D H s hs hF hL hd hLam
  exact coefficient_from_entries P a D H (regular P D H N d R L K)
    (fun key=>(2 : ℤ)^L key*commonAt P D H key^d key) EM ES

end LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicBits
