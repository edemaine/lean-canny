/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeNative
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutQueries
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
/-! # Native historical signs are the constructed full-tuple queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem evaluation (r : ℕ) (p : MvPolynomial ℕ ℤ[X]) (z : ℕ → ℝ) :
    (MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) p).eval₂ (Int.castRingHom ℝ) z =
      p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r)) z := by
  rw [MvPolynomial.eval₂_map]
  have h : (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) =
      SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
    · simp [SymbolicScaledSquarefree.scalarEvaluation]
  rw [h]

private theorem natural_heq {N M : ℕ} (h : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ) (he : HEq z w) :
    CoefficientFinitePhysicalQuery.natural z = CoefficientFinitePhysicalQuery.natural w := by
  cases h
  cases eq_of_heq he
  rfl

private theorem count_context (I J : SquareSampleInput.Inputs) (h : I = SquareSampleInput.comp J pairFst)
    (c d : List Bool) (hc : pairFst c = pairFst d) : I.count c = I.count d := by
  rw [h]
  exact congrArg J.count hc

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "I" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalTraceCutTest.value CoefficientMarkedRecordChoicePhysical.polynomial
  CoefficientMarkedRecordFullCutQueries.coefficientQuery

/-- Arbitrary same-root AUX, one OWN complete word, one entire tuple, and
literal full-factor coefficient requests; all metadata are derived. -/
theorem value (ctx aux w : List Bool) (q : CoefficientMarkedRecordFullCutQueries.CutLabel ctx)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (hw : SquareSampleCompleteVertices.Valid (I) (pair ctx aux) w)
    (he : q.coefficient ≤ 2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx)
    (hk : q.requested ≤ 2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx)
    (z : Fin (CoefficientMarkedRecordFullCutQueries.count hn ht ha ctx) → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (I) (pair ctx aux) w hw).val z) :
    IntegralMixedPhysicalTraceCutTest.value hn ht ha hR false
      (pair (pair (pair ctx aux) w) (IntegralFramedPhysicalTraceCutSource.datum
        (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx q.stage) true) q.coefficient q.requested)) =
      InfinitesimalSign.encode (SignType.sign ((CoefficientMarkedRecordFullCutQueries.coefficientQuery hn ht ha ctx q).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) z)) := by
  have hphysical := CoefficientMarkedRecordTraceProbeNative.physical_value hn ht ha hR (pair ctx aux) w hw
    q.stage (by simpa only [pairFst_pair] using q.stage_lt) q.coefficient q.requested
    (by simpa only [pairFst_pair] using he) (by simpa only [pairFst_pair] using hk)
  simp only [pairFst_pair] at hphysical
  have hp := CoefficientMarkedRecordTraceProbePhysical.specializes hn ht ha hR ctx q.stage q.stage_lt q.is_cut
    hlarge q.requested q.coefficient
  have hev := evaluation (R ctx)
    (CoefficientMarkedRecordChoicePhysical.polynomial hn ht ha ctx q.stage q.stage_lt.le q.requested q.coefficient)
    (CoefficientFinitePhysicalQuery.natural (SquareSampleCompleteVertices.candidate (I) (pair ctx aux) w hw).val)
  rw [hp] at hev
  have hc := count_context (I) (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR)
    (IntegralMixedPhysicalMarkedContext.input_factor hn ht ha hR) (pair ctx aux)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (by simp only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair])
  have hcount : (I).count (pair ctx aux) = CoefficientMarkedRecordFullCutQueries.count hn ht ha ctx :=
    hc.trans (CoefficientMarkedRecordCriticalFullSemantics.full_count hn ht ha hR ctx).symm
  have hnatur := natural_heq hcount _ z hz
  rw [hnatur] at hev
  have hquery := CoefficientMarkedRecordFullCutQueries.coefficient_evaluation hn ht ha ctx q ((2 : ℝ)^R ctx) z
  rw [hphysical]
  apply congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v))
  rw [hnatur]
  exact hev.trans hquery.symm

end LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeQuery
