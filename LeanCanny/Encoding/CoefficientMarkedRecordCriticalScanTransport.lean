/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalBranchSign
/-! # Fresh native whole-critical-scan words on one actual root branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCriticalScanTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem effective_le (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤
      CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans
    (CoefficientMarkedRecordCriticalBranchSign.row_cutoff_le hn ht ha ctx)

/-- The same actual row-root curve preserves the ENTIRE critical scan. -/
theorem zeros_on_curve (ctx : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (u v : Ioo a b) :
    CoefficientMarkedRecordCriticalFullSemantics.Zeros hn ht ha ctx u.val (x u) ↔
      CoefficientMarkedRecordCriticalFullSemantics.Zeros hn ht ha ctx v.val (x v) := by
  unfold CoefficientMarkedRecordCriticalFullSemantics.Zeros
  have hs := CoefficientMarkedRecordCriticalBranchSign.sign_on_root_curve hn ht ha ctx ha0 x hx
  constructor
  · intro h stage hb
    rw [← sign_eq_zero_iff, ← hs stage u v, sign_eq_zero_iff]
    exact h stage hb
  · intro h stage hb
    rw [← sign_eq_zero_iff, hs stage u v, sign_eq_zero_iff]
    exact h stage hb

/-- Any own native full word lifts to ONE actual full-row branch. The target
word is freshly sampled at the target radius on that same branch; every
critical correlation has the same truth value. No ordinal word is copied. -/
theorem transport_on_interval (ctx : List Bool) {R S : List Bool → ℕ}
    (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx ≤ a)
    (s u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) :
    ∃ x : C(Ioo a b, Fin (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx) → ℝ),
      (∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y)) ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val (x u) ∧
      ∃ w', ∃ hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w',
        w'.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
          (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
        HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
          (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v) ∧
        (pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR false ↔
          pair ctx w' ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hS false) := by
  have hRE := (effective_le hn ht ha ctx).trans hRlarge
  have hSE := (effective_le hn ht ha ctx).trans hSlarge
  obtain ⟨curve, _, hr, hc, _⟩ := CoefficientMarkedRecordCriticalBranchSign.exists_branches hn ht ha ctx ha0 s
  obtain ⟨z, hz, he⟩ := CoefficientMarkedRecordCriticalFullSemantics.rows_of_word hn ht ha hR ctx hRE w hw
  have hzu : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val z := hu.symm ▸ hz
  obtain ⟨l, hl, _⟩ := (hc u z).mp hzu
  have heU := he.trans (heq_of_eq hl.symm)
  have hvrow : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl ((2 : ℝ)^S ctx) (curve l.val v) := hv ▸ hr l v
  obtain ⟨w', hw', hlen, heV⟩ := CoefficientMarkedRecordFullRealization.exists_word hn ht ha ctx hS hSE (curve l.val v) hvrow
  refine ⟨curve l.val, hr l, heU, w', hw', hlen, heV, ?_⟩
  have hscanU := CoefficientMarkedRecordCriticalFullSemantics.packet_iff hn ht ha hR ctx hRE w hw (curve l.val u) heU
  have hscanV := CoefficientMarkedRecordCriticalFullSemantics.packet_iff hn ht ha hS ctx hSE w' hw' (curve l.val v) heV
  have hzero := zeros_on_curve hn ht ha ctx ha0 (curve l.val) (hr l) u v
  rw [hu, hv] at hzero
  exact hscanU.trans (hzero.trans hscanV.symm)

/-- Concrete radius-to-radius transport uses only the original cutoff and an
actual source word. The interval and root curve are constructed internally. -/
theorem transport_word (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx + 1 ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx + 1 ≤ S ctx)
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) :
    ∃ w', ∃ _hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w',
      w'.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
      (pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR false ↔
        pair ctx w' ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hS false) := by
  let a : ℝ := 2 ^ CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx
  let b : ℝ := max ((2 : ℝ)^R ctx) ((2 : ℝ)^S ctx) + 1
  have hu0 : a < (2 : ℝ)^R ctx := pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hRlarge)
  have hv0 : a < (2 : ℝ)^S ctx := pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hSlarge)
  let u : Ioo a b := ⟨(2 : ℝ)^R ctx, hu0, lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)⟩
  let v : Ioo a b := ⟨(2 : ℝ)^S ctx, hv0, lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)⟩
  obtain ⟨_, _, _, w', hw', hlen, _, hscan⟩ := transport_on_interval hn ht ha ctx hR hS
    (Nat.le_of_succ_le hRlarge) (Nat.le_of_succ_le hSlarge) (le_refl a) u u v rfl rfl w hw
  exact ⟨w', hw', hlen, hscan⟩

end LeanCanny.Encoding.CoefficientMarkedRecordCriticalScanTransport
