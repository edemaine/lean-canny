/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalParentContext
/-! # Fresh OWN physical tuples at both prepared critical prefixes -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalPrefixIncidence
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) =
      SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
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
  exact ⟨w, hv, (Classical.choose hv).1, heq_of_eq (congrArg (fun q : SquareSampleComplete.Roots S c => q.val)
    (SquareSampleCompleteVertices.candidate_word S hc c root))⟩

private theorem roots_of_data (B : IntegralFramedBankQuery.Bank) (c : List Bool)
    (E : CoefficientMarkedRecordRows.Data ℤ) (he : E = inputData B c)
    (w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    ∃ z : Fin E.count → ℝ, (∀ i, (E.rows i).eval₂ (Int.castRingHom ℝ) z = 0) ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val z := by
  cases he
  exact ⟨(SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val,
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).property, HEq.rfl⟩

private noncomputable def bankAt (B : IntegralFramedBankQuery.Bank) (key : List Bool → List Bool)
    (hp : ∀ q, 0 < (IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (key q)) :
    IntegralFramedBankQuery.Bank :=
  {B with key := key, positive := hp, coordinate q := ⟨0, hp q⟩}

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

private noncomputable def prefixBank (child : Bool) : IntegralFramedBankQuery.Bank :=
  bankAt (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false)
    (IntegralMixedPhysicalCriticalPrefixes.key n false child)
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha hR false child)

private theorem native_data (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) hR
      (CoefficientMarkedCriticalBankQuery.stage child q) q = inputData (prefixBank hn ht ha hR child) q := by
  change CoefficientMarkedRecordRowBounds.samplerData
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n := n) (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) q) =
    CoefficientMarkedRecordRowBounds.samplerData
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedPhysicalCriticalPrefixes.key n false child q)
  exact congrArg _ (CoefficientMarkedCriticalBankQuery.prefix_key n child q hc).symm

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedFramedHistoryFamilyBits.family CoefficientMarkedRecordRows.symbolic

/-- A genuine root of either actual symbolic prefix obtains its OWN complete
native word at that prefix, including every physical and multiplier column. -/
theorem exists_word (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count → ℝ)
    (hz : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q)) z) :
    ∃ w, ∃ hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w,
      w.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w hv).val z := by
  have hd := (CoefficientMarkedRecordRowBounds.map_certified hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) hR
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) q hlarge).trans (native_data hn ht ha hR child q hc)
  apply word_of_data (prefixBank hn ht ha hR child) q
    (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^R (IntegralMixedPhysicalCriticalQuery.root q)))
      (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _))) hd z
  intro i
  change (MvPolynomial.map (evalRingHom ((2 : ℤ)^R (IntegralMixedPhysicalCriticalQuery.root q)))
    ((CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).rows i)).eval₂ (Int.castRingHom ℝ) z = 0
  rw [MvPolynomial.eval₂_map, scalar_evaluation]
  exact hz i

/-- Conversely every valid OWN native prefix word lies in that same computed
symbolic row system. No arbitrary parent model or supplied root tuple is used. -/
theorem rows_of_word (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w) :
    ∃ z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count → ℝ,
      CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q)) z ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w hw).val z := by
  have hd := (CoefficientMarkedRecordRowBounds.map_certified hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) hR
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) q hlarge).trans (native_data hn ht ha hR child q hc)
  obtain ⟨z, hz, he⟩ := roots_of_data (prefixBank hn ht ha hR child) q
    (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^R (IntegralMixedPhysicalCriticalQuery.root q)))
      (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _))) hd w hw
  change Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count → ℝ at z
  refine ⟨z, ?_, he⟩
  intro i
  have hi := hz i
  change (MvPolynomial.map (evalRingHom ((2 : ℤ)^R (IntegralMixedPhysicalCriticalQuery.root q)))
    ((CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).rows i)).eval₂ (Int.castRingHom ℝ) z = 0 at hi
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at hi
  exact hi

end LeanCanny.Encoding.CoefficientMarkedCriticalPrefixIncidence
