/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermCoefficient
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProducts
/-! # Current-Q costs for literal common-cleared bank-term coefficients

The integer prelude may be implicit. Native producer-leading/cofactor readers
supply every scalar; no serialized original integer polynomial is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQBankTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankTermBits
open scoped Classical
variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
  (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
include a Hnew c hb

theorem coordinate_evaluator (W : List Bool→ℕ) (hW : UnaryFn W) :
    SpaceFunction (IntegralMixedFramedBankCoordinateBits.coefficient P D H W) := by
  have EC := IntegralMixedFramedCurrentQBankProductBits.evaluator P a D H Hnew c hb IntegralMixedFramedBankDenominatorBits.index
    IntegralMixedFramedBankDenominatorBits.index_binary
  have EE := EC.withInput.postcompose (IntegralMixedFramedBankCoordinateBits.finish P D H W) (IntegralMixedFramedBankCoordinateBits.finish_FP P a D H W hW)
  exact EE.congr (funext fun q => by
    simp only [Function.comp_apply,IntegralMixedFramedBankCoordinateBits.finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact (IntegralMixedFramedBankCoordinateBits.coefficient_selected P D H W q hq).symm
    · exact (IntegralMixedFramedBankCoordinateBits.coefficient_outside P D H W q hq).symm)

theorem numerator_evaluator (word : List Bool→List Bool) (hw : word∈FP) : SpaceFunction (numeratorCode P D H word) := by
  have EN := coordinate_evaluator P a D H Hnew c hb _ (coefficientWidth_unary P a D H word hw)
  exact (SpaceFunction.branch _ (active_FP P a D H).flag_mem_FP
    (EN.precompose _ (numeratorPacket_FP P a D H)) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun z => by simp only [numeratorCode,decide_eq_true_eq,Function.comp_apply])

theorem common_evaluator : SpaceFunction (commonCode P D H) :=
  (IntegralMixedFramedCurrentQBankProductBits.common_evaluator P a D H Hnew c hb).congr
    (funext fun q=>congrArg (fun z : ℤ=>residueBits (z : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
      (IntegralMixedFramedBankSnapshotBits.common_at P D H q))

theorem denominator_evaluator : SpaceFunction (denominatorCode P D H) := by
  have ED := common_evaluator P a D H Hnew c hb
  have HG := queriedDegree_binary.eq (BinaryFn.const 0)
  exact (SpaceFunction.branch _ HG.flag_mem_FP (ED.precompose _ denominatorPacket_FP)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun z => by simp only [denominatorCode,decide_eq_true_eq,Function.comp_apply])

theorem encoded_evaluator (word : List Bool→List Bool) (hw : word∈FP) :
    SpaceFunction (coordinates P D H word).family.value :=
  (coordinates P D H word).evaluator (ETR.RationalSubstitutionBits.Source.ofTerm_polyTime (wordAt_FP word hw))
    (numerator_evaluator P a D H Hnew c hb word hw) (denominator_evaluator P a D H Hnew c hb)

theorem coefficient_evaluator (word : List Bool→List Bool) (hw : word∈FP) :
    SpaceFunction (coefficient P D H word) := by
  have E:=encoded_evaluator P a D H Hnew c hb word hw
  have EP : SpaceFunction (PrimitivePairBits.coefficient (coordinates P D H word).family.polynomial):=
    E.congr (funext fun _=>rfl)
  exact (EP.precompose _ (coefficientQuery_FP P a D H word hw)).congr (funext fun q=>coefficient_packet P D H word q)

end LeanCanny.Algebra.IntegralMixedFramedCurrentQBankTermBits
