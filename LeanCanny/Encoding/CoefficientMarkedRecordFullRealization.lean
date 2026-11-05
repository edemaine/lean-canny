/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest
public import LeanCanny.Algebra.SymbolicScaledSquarefreeSmall
/-! # Fresh actual full words for the constructed symbolic full-row roots

Complete sampling is instantiated at the actual target radius and full bank.
The source tuple is preserved in full; its ordinal word is never transported.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullRealization
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) =
      SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [SymbolicScaledSquarefree.scalarEvaluation]
  · simp [SymbolicScaledSquarefree.scalarEvaluation]

private noncomputable def inputData (B : IntegralFramedBankQuery.Bank) (c : List Bool) :=
  CoefficientMarkedRecordRowBounds.samplerData B.parameters B.plan B.data (B.key c)

private theorem word_of_data (B : IntegralFramedBankQuery.Bank) (c : List Bool)
    (E : CoefficientMarkedRecordRows.Data ℤ) (he : E = inputData B c)
    (z : Fin E.count → ℝ) (hz : ∀ i, (E.rows i).eval₂ (Int.castRingHom ℝ) z = 0) :
    ∃ w, ∃ hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w,
      w.length = SquareSampleCompleteVertices.width (IntegralFramedPhysicalBankTerm.input B) c ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val z := by
  cases he
  let S := IntegralFramedPhysicalBankTerm.input B
  have hc : SquareSampleComplete.Complete S :=
    IntegralFramedPhysicalSquare.complete B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive
  let root : SquareSampleComplete.Roots S c := ⟨z, hz⟩
  let w := SquareSampleCompleteVertices.word S hc c root
  have hv := SquareSampleCompleteVertices.word_valid S hc c root
  refine ⟨w, hv, (Classical.choose hv).1, ?_⟩
  exact heq_of_eq (congrArg (fun q : SquareSampleComplete.Roots S c => q.val)
    (SquareSampleCompleteVertices.candidate_word S hc c root))

private theorem full_key (n : List Bool → ℕ) (c : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c) (IntegralMixedCausalRecordPlanBits.count (pairFst c)) [] =
      IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c := by
  unfold CoefficientMarkedRecordRowLayout.key IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedFramedHistoryFamilyBits.family CoefficientMarkedRecordRows.symbolic

private theorem native_data_full (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) :
    CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha ctx hR (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      inputData (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) := by
  change CoefficientMarkedRecordRowBounds.samplerData
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) []) =
    CoefficientMarkedRecordRowBounds.samplerData
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (IntegralMixedPhysicalMarkedTest.sampleContext ctx))
  apply congrArg
  simpa only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair] using
    full_key n (IntegralMixedPhysicalMarkedTest.sampleContext ctx)

/-- Original syntax and a genuine symbolic full-row root suffice for one fresh
OWN valid native word at the actual requested radius, with every raw coordinate. -/
theorem exists_word (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ)
    (hz : ∀ i, ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).rows i).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) z = 0) :
    ∃ w, ∃ hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w,
      w.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val z := by
  have hd := (CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx hR
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hlarge).trans (native_data_full hn ht ha ctx hR)
  apply word_of_data (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)
    (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^R ctx))
      (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl)) hd z
  intro i
  change (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
    ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).rows i)).eval₂
      (Int.castRingHom ℝ) z = 0
  rw [MvPolynomial.eval₂_map, scalar_evaluation]
  exact hz i

end LeanCanny.Encoding.CoefficientMarkedRecordFullRealization
