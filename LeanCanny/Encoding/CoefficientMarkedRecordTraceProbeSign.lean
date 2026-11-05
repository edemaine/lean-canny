/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutSign
/-! # Literal native coefficient readers on one radius-parametrized branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem effective_le (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤
      CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans
    (CoefficientMarkedRecordFullCutSign.row_cutoff_le hn ht ha ctx)

/-- Both readers use their OWN words and the SAME full-row curve. All
coefficient and clipped-choice requests in the literal guard range agree. -/
theorem value_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (aux aux' w w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx aux) w)
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (pair ctx aux') w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (pair ctx aux) w hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (pair ctx aux') w' hw').val (x v))
    (q : CoefficientMarkedRecordFullCutQueries.CutLabel ctx)
    (he : q.coefficient ≤ 2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx)
    (hk : q.requested ≤ 2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx) :
    IntegralMixedPhysicalTraceCutTest.value hn ht ha hR false
      (pair (pair (pair ctx aux) w) (IntegralFramedPhysicalTraceCutSource.datum
        (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx q.stage) true) q.coefficient q.requested)) =
    IntegralMixedPhysicalTraceCutTest.value hn ht ha hS false
      (pair (pair (pair ctx aux') w') (IntegralFramedPhysicalTraceCutSource.datum
        (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx q.stage) true) q.coefficient q.requested)) := by
  rw [CoefficientMarkedRecordTraceProbeQuery.value hn ht ha hR ctx aux w q
      ((effective_le hn ht ha ctx).trans hRlarge) hw he hk (x u) hz,
    CoefficientMarkedRecordTraceProbeQuery.value hn ht ha hS ctx aux' w' q
      ((effective_le hn ht ha ctx).trans hSlarge) hw' he hk (x v) hz']
  have h := CoefficientMarkedRecordFullCutSign.sign_on_root_curve hn ht ha ctx ha0 x hx (.inr q) u v
  change SignType.sign ((CoefficientMarkedRecordFullCutQueries.coefficientQuery hn ht ha ctx q).eval₂
    (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((CoefficientMarkedRecordFullCutQueries.coefficientQuery hn ht ha ctx q).eval₂
    (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) at h
  rw [hu, hv] at h
  exact congrArg InfinitesimalSign.encode h

end LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeSign
