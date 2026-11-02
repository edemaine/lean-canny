/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankProducts
public import LeanCanny.Algebra.ModularResidueSpace
/-! # Charged old-bank scalars for the two marked slack matrices

Q is the actual old common denominator, obtained by its native product pass.
Original binary exponents stay implicit. All arithmetic is modulo the same
caller modulus, including nonunits and modulus one.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def powerPost (mw : List Bool → List Bool) (e : List Bool → ℕ) (z : List Bool) :=
  BinaryNat.powMod (pair (pairSnd z) (pair (BinaryNatCode.encode (e (pairFst z))) (mw (pairFst z))))

theorem powerPost_FP {mw : List Bool → List Bool} (hm : mw∈FP) {e : List Bool → ℕ} (he : BinaryFn e) : powerPost mw e∈FP := by
  have HE : BinaryFn (fun z=>e (pairFst z)) := he.comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_pair HE.bits_mem_FP
    (mem_FP_comp (f := pairFst) (g := mw) pairFst_mem_FP hm))) BinaryNat.powMod_mem_FP

theorem power_evaluator {mw : List Bool → List Bool} (hm : mw∈FP) {e : List Bool → ℕ} (he : BinaryFn e)
    {v : (q : List Bool) → ZMod (ModularResidueSpace.m mw q)} (E : SpaceFunction (fun q=>residueBits (v q))) :
    SpaceFunction (fun q=>residueBits (v q^e q)) := by
  refine (E.withInput.postcompose (powerPost mw e) (powerPost_FP hm he)).congr (funext fun q=>?_)
  simp only [Function.comp_apply,powerPost,pairFst_pair,pairSnd_pair]
  simpa only [BinaryNatCode.encode,Nat.fromBitsLE_bits] using ArithmeticBits.powMod_residueBits (mw q) (BinaryNatCode.encode (e q)) (v q)

theorem dyadic_evaluator {mw : List Bool → List Bool} (hm : mw∈FP) {e : List Bool → ℕ} (he : BinaryFn e) :
    SpaceFunction (fun q=>residueBits (((2 : ℤ)^e q : ℤ) : ZMod (ModularResidueSpace.m mw q))) := by
  have HD := (BinaryFn.const 2).powModSucc he (BinaryFn.fromBits hm)
  refine (SpaceFunction.ofFP _ HD.bits_mem_FP).congr (funext fun q=>?_)
  have HC : (((2 : ℤ)^e q : ℤ) : ZMod (ModularResidueSpace.m mw q))=
      (((2 : ℕ)^e q : ℕ) : ZMod (ModularResidueSpace.m mw q)) := by
    simp only [Int.cast_pow,Nat.cast_pow,Int.cast_ofNat,Nat.cast_ofNat]
  rw [HC]
  simp only [residueBits,ZMod.val_natCast]

noncomputable def common (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  IntegralMixedHistory.commonDenominator ((IntegralMixedFramedHistoryFamilyBits.family P D H).state (PaddedIntegralGeneratorSource.base q))

noncomputable def sphereDiagonal (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : List Bool → ℕ) (q : List Bool) : ℤ := common P D H q^2*((2 : ℤ)^R (PaddedIntegralGeneratorSource.base q))^2
noncomputable def regularScale (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (d L : List Bool → ℕ) (q : List Bool) : ℤ := (2 : ℤ)^L (PaddedIntegralGeneratorSource.base q)*common P D H q^d (PaddedIntegralGeneratorSource.base q)
noncomputable def regularDiagonal (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (d L K : List Bool → ℕ) (q : List Bool) : ℤ :=
  regularScale P D H d L q*(2 : ℤ)^K (PaddedIntegralGeneratorSource.base q)+common P D H q^d (PaddedIntegralGeneratorSource.base q)

theorem common_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hN : ∀ root,1≤s.nodes root) :
    SpaceFunction (fun q=>residueBits (common P D H q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
  IntegralMixedFramedBankProductBits.common_evaluator P a D H s hs hF hN

theorem sphere_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hN : ∀ root,1≤s.nodes root) {R : List Bool → ℕ} (hR : BinaryFn R) :
    SpaceFunction (fun q=>residueBits (sphereDiagonal P D H R q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) := by
  have EQ := power_evaluator PaddedIntegralGeneratorSource.modulus_FP (BinaryFn.const 2) (common_space P a D H s hs hF hN)
  have ED := dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP (hR.comp PaddedIntegralGeneratorSource.base_FP)
  have ER := power_evaluator PaddedIntegralGeneratorSource.modulus_FP (BinaryFn.const 2) ED
  have EE := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _
    PaddedIntegralGeneratorSource.modulus_FP EQ ER
  exact EE.congr (funext fun q=>by simp only [sphereDiagonal,Int.cast_mul,Int.cast_pow,Function.comp_apply])

theorem regularScale_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hN : ∀ root,1≤s.nodes root)
    {d L : List Bool → ℕ} (hd : BinaryFn d) (hL : BinaryFn L) :
    SpaceFunction (fun q=>residueBits (regularScale P D H d L q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) := by
  have EQ := power_evaluator PaddedIntegralGeneratorSource.modulus_FP (hd.comp PaddedIntegralGeneratorSource.base_FP)
    (common_space P a D H s hs hF hN)
  have EL := dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP (hL.comp PaddedIntegralGeneratorSource.base_FP)
  have EE := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _
    PaddedIntegralGeneratorSource.modulus_FP EL EQ
  exact EE.congr (funext fun q=>by simp only [regularScale,Int.cast_mul,Int.cast_pow,Function.comp_apply])

theorem regularDiagonal_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hN : ∀ root,1≤s.nodes root)
    {d L K : List Bool → ℕ} (hd : BinaryFn d) (hL : BinaryFn L) (hK : BinaryFn K) :
    SpaceFunction (fun q=>residueBits (regularDiagonal P D H d L K q : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) := by
  have EL := regularScale_space P a D H s hs hF hN hd hL
  have EK := dyadic_evaluator PaddedIntegralGeneratorSource.modulus_FP (hK.comp PaddedIntegralGeneratorSource.base_FP)
  have EP := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _ PaddedIntegralGeneratorSource.modulus_FP EL EK
  have EQ := power_evaluator PaddedIntegralGeneratorSource.modulus_FP (hd.comp PaddedIntegralGeneratorSource.base_FP)
    (common_space P a D H s hs hF hN)
  have EE := ModularResidueSpace.addEvaluator PaddedIntegralGeneratorSource.modulus _ _ PaddedIntegralGeneratorSource.modulus_FP EP EQ
  exact EE.congr (funext fun q=>by simp only [regularDiagonal,Int.cast_add,Int.cast_mul,Int.cast_pow,Function.comp_apply])

end LeanCanny.Algebra.IntegralMixedFramedSlackScalarBits
