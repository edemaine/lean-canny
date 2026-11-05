/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceBeforeTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordMarkedTransport
/-! # Fresh own words preserve marked original tests and both historical scans -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordMarkedWordTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordFullCutTransport.cutoff hn ht ha ctx +
  CoefficientMarkedRecordMarkedTransport.cutoff hn ht ha ctx

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  (CoefficientMarkedRecordFullCutTransport.cutoff_binary hn ht ha).add
    (CoefficientMarkedRecordMarkedTransport.cutoff_binary hn ht ha)

/-- The interval, complete branch and target OWN word are constructed
internally. The SAME fresh word preserves all marked original tests and both whole native scans. -/
theorem transport_word (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx + 1 ≤ R ctx)
    (hSlarge : cutoff hn ht ha ctx + 1 ≤ S ctx)
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) :
    ∃ w', ∃ _hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w',
      w'.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
      (pair ctx w ∈ IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha hR false ↔
        pair ctx w' ∈ IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha hS false) ∧
      (pair ctx w ∈ IntegralMixedPhysicalMarkedTest.language hn ht ha hR false ↔
        pair ctx w' ∈ IntegralMixedPhysicalMarkedTest.language hn ht ha hS false) ∧
      (pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR false ↔
        pair ctx w' ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hS false) := by
  let a : ℝ := 2 ^ cutoff hn ht ha ctx
  let b : ℝ := max ((2 : ℝ)^R ctx) ((2 : ℝ)^S ctx) + 1
  have hu0 : a < (2 : ℝ)^R ctx := pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hRlarge)
  have hv0 : a < (2 : ℝ)^S ctx := pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hSlarge)
  let u : Ioo a b := ⟨(2 : ℝ)^R ctx, hu0, lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)⟩
  let v : Ioo a b := ⟨(2 : ℝ)^S ctx, hv0, lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)⟩
  have hf : CoefficientMarkedRecordFullCutTransport.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := Nat.le_add_right _ _
  have hl : CoefficientMarkedRecordMarkedTransport.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := Nat.le_add_left _ _
  have haf : (2 : ℝ)^CoefficientMarkedRecordFullCutTransport.cutoff hn ht ha ctx ≤ a :=
    pow_le_pow_right₀ (by norm_num) hf
  obtain ⟨x, hx, hz, w', hw', hlen, hz', hcritical, _⟩ :=
    CoefficientMarkedRecordFullCutTransport.transport_on_interval hn ht ha ctx hR hS
      (hf.trans (Nat.le_of_succ_le hRlarge)) (hf.trans (Nat.le_of_succ_le hSlarge)) haf u u v rfl rfl w hw
  have hcut : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤
      CoefficientMarkedRecordFullCutTransport.cutoff hn ht ha ctx := Nat.le_add_right _ _
  have ha0 : (2 : ℝ)^CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ a :=
    pow_le_pow_right₀ (by norm_num) (hcut.trans hf)
  have hbefore := CoefficientMarkedRecordTraceBeforeTransport.holds_on_curve hn ht ha ctx hR hS
    ((hcut.trans hf).trans (Nat.le_of_succ_le hRlarge)) ((hcut.trans hf).trans (Nat.le_of_succ_le hSlarge))
    ha0 x hx u v rfl rfl w w' hw hw' hz hz'
  have haleaf : (2 : ℝ)^CoefficientMarkedRecordMarkedTransport.cutoff hn ht ha ctx ≤ a :=
    pow_le_pow_right₀ (by norm_num) hl
  have hleaves := CoefficientMarkedRecordMarkedTransport.language_on_curve hn ht ha ctx hR hS
    (hl.trans (Nat.le_of_succ_le hRlarge)) (hl.trans (Nat.le_of_succ_le hSlarge))
    haleaf x hx u v rfl rfl w w' hw hw' hz hz'
  refine ⟨w', hw', hlen, ?_, hleaves, hcritical⟩
  change (SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
    (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst (pair ctx w))) (pairSnd (pair ctx w)) ∧
    IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha hR false (pair ctx w)) ↔
    (SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
    (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst (pair ctx w'))) (pairSnd (pair ctx w')) ∧
    IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha hS false (pair ctx w'))
  simpa only [pairFst_pair, pairSnd_pair, hw, hw', true_and] using hbefore

end LeanCanny.Encoding.CoefficientMarkedRecordMarkedWordTransport
