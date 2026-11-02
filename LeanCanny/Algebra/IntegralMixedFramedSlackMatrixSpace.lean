/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrices
public import LeanCanny.Algebra.IntegralMixedFramedMatrixValuePower
/-! # Native U/V entries from original source data

Old-height and denominator controllers close all matrix/scalar child costs.
Only original count and binary exponent controls remain; no current matrix,
Q, leading, height or evaluator cost is a premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedHistory.commonDenominator

noncomputable def sphereValue (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N R : List Bool → ℕ) := IntegralMixedFramedMatrixValueBits.value P D H (sphere P D H N R)
noncomputable def regularValue (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N d R L K : List Bool → ℕ) := IntegralMixedFramedMatrixValueBits.value P D H (regular P D H N d R L K)

theorem sphere_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {N R : List Bool → ℕ} (hN : UnaryFn N) (hR : BinaryFn R) : SpaceFunction (sphereValue P D H N R) := by
  have EA : SpaceFunction (fun q=>residueBits (sphereCoefficient P D H R (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    IntegralMixedFramedSlackScalarBits.sphere_space P a D H s hs hF hL hR
  have ED := IntegralMixedFramedMatrixValueBits.diagonal_evaluator P D H a EA
  have ES : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H
      (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N (fun _=>2))) :=
    IntegralMixedFramedClearedPowerSumBits.evaluator P a D H s hs hF hL hN (BinaryFn.const 2)
  exact IntegralMixedFramedMatrixValueBits.sub_evaluator P D H ED ES

theorem regular_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {N d R L K : List Bool → ℕ} (hN : UnaryFn N) (hd : BinaryFn d) (hR : BinaryFn R) (hLam : BinaryFn L) (hK : BinaryFn K) :
    SpaceFunction (regularValue P D H N d R L K) := by
  have EA : SpaceFunction (fun q=>residueBits (regularCoefficient P D H d L K (PaddedIntegralGeneratorSource.base q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    IntegralMixedFramedSlackScalarBits.regularDiagonal_space P a D H s hs hF hL hd hLam hK
  have ED := IntegralMixedFramedMatrixValueBits.diagonal_evaluator P D H a EA
  have ES : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H
      (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N d)) :=
    IntegralMixedFramedClearedPowerSumBits.evaluator P a D H s hs hF hL hN hd
  have EL : SpaceFunction (fun q=>residueBits (((2 : ℤ)^L (PaddedIntegralGeneratorSource.base q) : ℤ) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    IntegralMixedFramedSlackScalarBits.dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP
      (hLam.comp PaddedIntegralGeneratorSource.base_FP)
  have ESS := IntegralMixedFramedMatrixValueBits.smul_evaluator P D H (f := fun key=>(2 : ℤ)^L key) EL ES
  have EU : SpaceFunction (IntegralMixedFramedMatrixValueBits.value P D H (sphere P D H N R)) :=
    sphere_evaluator P a D H s hs hF hL hN hR
  have EUP := IntegralMixedFramedMatrixValueBits.power_evaluator P a D H (hd.div (BinaryFn.const 2)) EU
  have EUPS := IntegralMixedFramedMatrixValueBits.smul_evaluator P D H (f := fun key=>(2 : ℤ)^L key) EL EUP
  exact IntegralMixedFramedMatrixValueBits.sub_evaluator P D H
    (IntegralMixedFramedMatrixValueBits.sub_evaluator P D H ED ESS) EUPS

end LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBits
