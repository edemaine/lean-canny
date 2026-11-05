/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafTransport
/-! # The entire native original marked test on one shared full-row branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordMarkedTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem probe_packet (ctx w : List Bool) :
    IntegralMixedPhysicalMarkedTest.probe (pair ctx w) = pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) [] := by
  simp only [IntegralMixedPhysicalMarkedTest.probe, IntegralMixedPhysicalMarkedTest.leafQuery, pairFst_pair, pairSnd_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx +
  CoefficientMarkedRecordTermSign.cutoff hn ht ha (IntegralMixedMarkedPointTest.regularWord n t) ctx +
  CoefficientMarkedRecordTermSign.cutoff hn ht ha (IntegralMixedMarkedPointTest.markWord n t) ctx

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((CoefficientMarkedRecordLeafSign.cutoff_binary hn ht ha).add
    (CoefficientMarkedRecordTermSign.cutoff_binary hn ht ha _ (IntegralMixedMarkedPointTest.regularWord_FP hn ht))).add
    (CoefficientMarkedRecordTermSign.cutoff_binary hn ht ha _ (IntegralMixedMarkedPointTest.markWord_FP hn ht))

private theorem leaf_le (ctx : List Bool) : CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega
private theorem regular_le (ctx : List Bool) :
    CoefficientMarkedRecordTermSign.cutoff hn ht ha (IntegralMixedMarkedPointTest.regularWord n t) ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega
private theorem mark_le (ctx : List Bool) :
    CoefficientMarkedRecordTermSign.cutoff hn ht ha (IntegralMixedMarkedPointTest.markWord n t) ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

theorem regular_value {R : List Bool → ℕ} (hR : BinaryFn R) (ctx w : List Bool) :
    IntegralMixedPhysicalMarkedTest.regularValue hn ht ha hR false (pair ctx w) =
      CoefficientMarkedRecordTermValue.value hn ht ha hR (IntegralMixedMarkedPointTest.regularWord n t) ctx w := by
  unfold IntegralMixedPhysicalMarkedTest.regularValue
  simp only [Function.comp_apply, probe_packet]
  rfl

theorem mark_value {R : List Bool → ℕ} (hR : BinaryFn R) (ctx w : List Bool) :
    IntegralMixedPhysicalMarkedTest.markValue hn ht ha hR false (pair ctx w) =
      CoefficientMarkedRecordTermValue.value hn ht ha hR (IntegralMixedMarkedPointTest.markWord n t) ctx w := by
  unfold IntegralMixedPhysicalMarkedTest.markValue
  simp only [Function.comp_apply, probe_packet]
  rfl

/-- Original leaves, regularity and the mark are preserved simultaneously on
ONE actual branch with both complete own words, not independently sampled. -/
theorem language_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordLeafSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (w w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v)) :
    pair ctx w ∈ IntegralMixedPhysicalMarkedTest.language hn ht ha hR false ↔
      pair ctx w' ∈ IntegralMixedPhysicalMarkedTest.language hn ht ha hS false := by
  have hleaf := CoefficientMarkedRecordLeafTransport.leaves_on_curve hn ht ha ctx hR hS
    ((leaf_le hn ht ha ctx).trans hRlarge) ((leaf_le hn ht ha ctx).trans hSlarge)
    ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (leaf_le hn ht ha ctx)).trans ha0)
    x hx u v hu hv w w' hw hw' hz hz'
  have hregular := CoefficientMarkedRecordTermTransport.value_on_curve hn ht ha
    (IntegralMixedMarkedPointTest.regularWord n t) ctx hR hS
    ((regular_le hn ht ha ctx).trans hRlarge) ((regular_le hn ht ha ctx).trans hSlarge)
    ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (regular_le hn ht ha ctx)).trans ha0)
    x hx u v hu hv w w' hw hw' hz hz'
  have hmark := CoefficientMarkedRecordTermTransport.value_on_curve hn ht ha
    (IntegralMixedMarkedPointTest.markWord n t) ctx hR hS
    ((mark_le hn ht ha ctx).trans hRlarge) ((mark_le hn ht ha ctx).trans hSlarge)
    ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mark_le hn ht ha ctx)).trans ha0)
    x hx u v hu hv w w' hw hw' hz hz'
  change (pair ctx w ∈ IntegralMixedPhysicalMarkedTest.leaves hn ht ha hR false ∧
    IntegralMixedPhysicalMarkedTest.regularValue hn ht ha hR false (pair ctx w) = InfinitesimalSign.encode 0 ∧
    IntegralMixedPhysicalMarkedTest.markValue hn ht ha hR false (pair ctx w) = InfinitesimalSign.encode 0) ↔
    (pair ctx w' ∈ IntegralMixedPhysicalMarkedTest.leaves hn ht ha hS false ∧
    IntegralMixedPhysicalMarkedTest.regularValue hn ht ha hS false (pair ctx w') = InfinitesimalSign.encode 0 ∧
    IntegralMixedPhysicalMarkedTest.markValue hn ht ha hS false (pair ctx w') = InfinitesimalSign.encode 0)
  rw [regular_value hn ht ha hR, regular_value hn ht ha hS, mark_value hn ht ha hR, mark_value hn ht ha hS,
    hleaf, hregular, hmark]

end LeanCanny.Encoding.CoefficientMarkedRecordMarkedTransport
