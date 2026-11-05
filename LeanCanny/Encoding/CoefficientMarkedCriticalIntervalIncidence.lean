/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalQuery
public import LeanCanny.Encoding.CoefficientMarkedCriticalPrefixIncidence
/-! # Both critical interval tests use the SAME complete child tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalIntervalIncidence
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem columns_eq (B : IntegralFramedBankQuery.Bank)
    (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (word : List Bool → List Bool) (c d : List Bool) :
    IntegralFramedPhysicalBankTerm.columns B T hr word c d =
      (IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data (B.key c)).scalar := by
  unfold IntegralFramedPhysicalBankTerm.columns
  rw [IntegralMixedFramedPhysicalIndex.nativeScalarColumn_eq]
  rfl

private theorem eval_physical (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool)
    (z : Fin (IntegralFramedPhysicalSquare.count P D key) → ℝ) :
    (CoefficientMarkedCriticalIntervalQuery.physicalQuery P D H word key).eval₂ (Int.castRingHom ℝ) z =
      (IntegralMixedFramedBankTermBits.polynomial P D H word key).eval₂ (Int.castRingHom ℝ)
        (fun i => z ((IntegralFramedPhysicalSquare.sampler P D H key).scalar i)) :=
  MvPolynomial.eval₂_rename _ _ _ _

private theorem packet_raw (B : IntegralFramedBankQuery.Bank)
    (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (word : List Bool → List Bool) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    IntegralFramedPhysicalBankTerm.value B T hr word (pair (pair c w) []) =
      InfinitesimalSign.encode (SignType.sign
        ((CoefficientMarkedCriticalIntervalQuery.physicalQuery B.parameters B.plan B.data word (B.key c)).eval₂
          (Int.castRingHom ℝ) (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val)) := by
  have hp := SquareSampleCompleteEmbeddedPolynomialTest.packet (IntegralFramedPhysicalBankTerm.input B)
    (IntegralFramedPhysicalBankTerm.source B word) (IntegralFramedPhysicalBankTerm.columns B T hr word) c w [] hv
  have he : ((IntegralFramedPhysicalBankTerm.source B word).polynomial c []).eval₂ (Int.castRingHom ℝ)
      (fun i => (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val
        (IntegralFramedPhysicalBankTerm.columns B T hr word c [] i)) =
      (CoefficientMarkedCriticalIntervalQuery.physicalQuery B.parameters B.plan B.data word (B.key c)).eval₂
        (Int.castRingHom ℝ) (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val := by
    rw [eval_physical, columns_eq]
    rfl
  exact hp.trans (congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) he)

private theorem eval_heq {N M : ℕ} (h : N = M)
    (p : MvPolynomial (Fin N) ℤ) (q : MvPolynomial (Fin M) ℤ) (hp : HEq p q)
    (z : Fin N → ℝ) (w : Fin M → ℝ) (hz : HEq z w) :
    p.eval₂ (Int.castRingHom ℝ) z = q.eval₂ (Int.castRingHom ℝ) w := by
  cases h
  cases eq_of_heq hp
  cases eq_of_heq hz
  rfl

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) =
      SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
  · simp [SymbolicScaledSquarefree.scalarEvaluation]

private theorem eval_mapped_heq {N M : ℕ} (h : N = M)
    (p : MvPolynomial (Fin N) ℤ[X]) (q : MvPolynomial (Fin M) ℤ) (r : ℕ)
    (hp : HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) p) q)
    (z : Fin N → ℝ) (w : Fin M → ℝ) (hz : HEq z w) :
    p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r)) z =
      q.eval₂ (Int.castRingHom ℝ) w := by
  have he := eval_heq h _ _ hp z w hz
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at he
  exact he

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem arguments_count (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    (CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx k hk).dimension =
      (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk).count := rfl

private theorem input_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (hp : ∀ c, 0 < (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
    (q : List Bool) : (IntegralFramedPhysicalSquare.input P D H L F C hs key hp).count q =
      IntegralFramedPhysicalSquare.count P D (key q) := rfl

private theorem planned_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralFramedPhysicalSquare.count (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key =
      IntegralFramedPhysicalSquare.count P D key := rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalMarkedPlan.bank CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedRecordTermQuery.arguments CoefficientMarkedCriticalIntervalQuery.polynomial

private theorem bank_count_base (key : List Bool) :
    IntegralFramedPhysicalSquare.count (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan key =
      IntegralFramedPhysicalSquare.count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) key := by
  have HB : IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR := by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    rfl
  rw [HB]
  exact planned_count _ _ _ _ _ _

private theorem count_eq (q : List Bool) :
    (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true).count q =
      (CoefficientMarkedRecordTermQuery.arguments hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl).dimension := by
  rw [arguments_count]
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  have h1 := input_count B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralMixedPhysicalCriticalPrefixes.key n false true)
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha hR false true) q
  have h3 := CoefficientMarkedRecordRowLayout.count_eq hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) R
    (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl q
  rw [← CoefficientMarkedCriticalIntervalQuery.child_key n q] at h3
  exact h1.trans ((bank_count_base hn ht ha hR _).trans h3)

/-- No interval or ordering premise is needed to identify either literal
endpoint sign on this same freshly sampled child-prefix tuple. -/
theorem value_eq (upper : Bool) (q : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w)
    (z : Fin (CoefficientMarkedRecordTermQuery.arguments hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl).dimension → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w hw).val z) :
    IntegralMixedPhysicalCriticalInterval.value hn ht ha hR false upper (pair q w) =
      InfinitesimalSign.encode (SignType.sign
        ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper (IntegralMixedPhysicalCriticalQuery.root q)).eval₂
          (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q))) z)) := by
  let B := IntegralMixedPhysicalCriticalInterval.childBank hn ht ha hR false
  have hp := CoefficientMarkedCriticalIntervalQuery.specializes hn ht ha upper hR q hlarge
  have he := eval_mapped_heq (count_eq hn ht ha hR q).symm _ _
    (R (IntegralMixedPhysicalCriticalQuery.root q)) hp z _ hz.symm
  unfold IntegralMixedPhysicalCriticalInterval.value
  simp only [Function.comp_apply, IntegralMixedPhysicalCriticalInterval.probe]
  exact (packet_raw B (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false)
    (IntegralMixedPhysicalCriticalInterval.word n false upper) q w hw).trans
      (congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) he.symm)

end LeanCanny.Encoding.CoefficientMarkedCriticalIntervalIncidence
