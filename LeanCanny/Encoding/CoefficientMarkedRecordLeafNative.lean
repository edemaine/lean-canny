/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafRecipe
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeNative
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafSign
/-! # Actual marked leaf queries at the certified full physical word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafNative
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem arguments_key (B : IntegralFramedBankQuery.Bank) (c key : List Bool) (hk : B.key c = key) :
    CoefficientMarkedRecordLeafRecipe.arguments B c =
    CoefficientBankTermQuery.ofSnapshot B.parameters B.plan B.data key
      (IntegralFramedPhysicalSquare.count B.parameters B.plan key)
      (IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data key).scalar := by
  unfold CoefficientMarkedRecordLeafRecipe.arguments
  rw [hk]

private theorem arguments_planned (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) :
    CoefficientBankTermQuery.ofSnapshot (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key
      (IntegralFramedPhysicalSquare.count (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key)
      (IntegralFramedPhysicalSquare.sampler (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
        (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key).scalar =
    CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
      (IntegralFramedPhysicalSquare.sampler P D H key).scalar := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build

theorem arguments_actual (ctx : List Bool) :
    CoefficientMarkedRecordLeafRecipe.arguments (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) =
    CoefficientMarkedRecordLeafQuery.nativeArguments hn ht ha ctx R
      (IntegralMixedCausalRecordPlanBits.count ctx) [] := by
  have hk := CoefficientMarkedRecordTraceProbeNative.terminal hn ht ha hR (IntegralMixedPhysicalMarkedTest.sampleContext ctx)
  simp only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair,
    CoefficientMarkedRecordRawCutMetadata.terminal] at hk
  have he := arguments_key (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) _ hk
  have hp := arguments_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) [])
  exact he.trans hp

noncomputable def polynomial (ctx : List Bool) (i : ℕ) :=
  CoefficientBankLeafQuery.polynomial
    (CoefficientMarkedRecordLeafRecipe.arguments (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx))
    ((IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false).polynomial
      (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (BinaryNatCode.encode i)))
    (2*(IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false).degree
      (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (BinaryNatCode.encode i))) i

private theorem polynomial_congr (A A' : CoefficientBankTermQuery.Arguments ℤ) (hA : A = A')
    (p q : ℤ[X]) (hp : p = q) (D E i : ℕ) (hD : D = E) :
    HEq (CoefficientBankLeafQuery.polynomial A p D i) (CoefficientBankLeafQuery.polynomial A' q E i) := by
  cases hA
  cases hp
  cases hD
  rfl

/-- Actual certified source metadata and planned physical bank are derived
from the same original full prefix, including every total index. -/
theorem polynomial_actual (ctx : List Bool) (i : ℕ) :
    HEq (polynomial hn ht ha hR ctx i)
      (CoefficientMarkedRecordLeafQuery.nativePolynomial hn ht ha ctx R
        (IntegralMixedCausalRecordPlanBits.count ctx) [] i) := by
  have hp : (IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false).polynomial
      (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (BinaryNatCode.encode i)) =
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
        (CoefficientMarkedRecordLeafQuery.sourceKey ctx i) :=
    IntegralMixedPhysicalMarkedPlan.source_packet hn ht ha (R := R) false ctx i
  have hd : (IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false).degree
      (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (BinaryNatCode.encode i)) =
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).degree
        (CoefficientMarkedRecordLeafQuery.sourceKey ctx i) := by
    change (IntegralFramedPhysicalLeafSources.marked hn ht ha R).degree
      (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (BinaryNatCode.encode i)) = _
    simp only [IntegralFramedPhysicalLeafSources.marked, IntegralFramedPhysicalLeafSources.source,
      IntegerPolynomialSourceChoice.reindex, Function.comp_apply, IntegralFramedPhysicalLeafSources.query,
      IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair, pairSnd_pair, CoefficientMarkedRecordLeafQuery.sourceKey]
  exact polynomial_congr _ _ (arguments_actual hn ht ha hR ctx) _ _ hp _ _ i (congrArg (2*·) hd)

/-- The literal actual full-word leaf polynomial is the dyadic specialization
of the original bounded query; no supplied native model is identified. -/
theorem specializes (ctx : List Bool) (i : ℕ)
    (hi : i < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (CoefficientMarkedRecordLeafSign.polynomial hn ht ha ctx
        ⟨i, hi⟩))
      (polynomial hn ht ha hR ctx i) := by
  exact (CoefficientMarkedRecordLeafQuery.specializes hn ht ha ctx R
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i hlarge).trans
      (polynomial_actual hn ht ha hR ctx i).symm

end LeanCanny.Encoding.CoefficientMarkedRecordLeafNative
