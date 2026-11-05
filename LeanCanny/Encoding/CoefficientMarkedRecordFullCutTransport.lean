/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalScanTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutSign
/-! # Fresh native words preserve critical scans and every historical cut probe -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (ctx : List Bool) :=
  CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx + CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  (CoefficientMarkedRecordFullCutSign.cutoff_binary hn ht ha).add
    (CoefficientMarkedRecordCriticalBranchSign.cutoff_binary hn ht ha)

private theorem effective_le (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx :=
  ((CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans
    (CoefficientMarkedRecordCriticalBranchSign.row_cutoff_le hn ht ha ctx)).trans (Nat.le_add_left _ _)

/-- Any own native full word lifts to ONE actual full-row branch. The target
word is freshly sampled at the target radius on that same branch; every
critical correlation and every historical cut/coordinate query keeps its sign. No ordinal word is copied. -/
theorem transport_on_interval (ctx : List Bool) {R S : List Bool → ℕ}
    (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
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
          pair ctx w' ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hS false) ∧
        (∀ q : CoefficientMarkedRecordFullCutQueries.Label hn ht ha ctx,
          SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx q).eval₂
            (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
          SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx q).eval₂
            (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v))) := by
  have hRE := (effective_le hn ht ha ctx).trans hRlarge
  have hSE := (effective_le hn ht ha ctx).trans hSlarge
  have hcut : (2 : ℝ)^CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_right _ _)).trans ha0
  have hcritical : (2 : ℝ)^CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_left _ _)).trans ha0
  obtain ⟨curve, _, hr, hc, hs⟩ := CoefficientMarkedRecordFullCutSign.exists_branches hn ht ha ctx hcut s
  obtain ⟨z, hz, he⟩ := CoefficientMarkedRecordCriticalFullSemantics.rows_of_word hn ht ha hR ctx hRE w hw
  have hzu : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val z := hu.symm ▸ hz
  obtain ⟨l, hl, _⟩ := (hc u z).mp hzu
  have heU := he.trans (heq_of_eq hl.symm)
  have hvrow : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl ((2 : ℝ)^S ctx) (curve l.val v) := hv ▸ hr l v
  obtain ⟨w', hw', hlen, heV⟩ := CoefficientMarkedRecordFullRealization.exists_word hn ht ha ctx hS hSE (curve l.val v) hvrow
  refine ⟨curve l.val, hr l, heU, w', hw', hlen, heV, ?_, fun q => hs l q u v⟩
  have hscanU := CoefficientMarkedRecordCriticalFullSemantics.packet_iff hn ht ha hR ctx hRE w hw (curve l.val u) heU
  have hscanV := CoefficientMarkedRecordCriticalFullSemantics.packet_iff hn ht ha hS ctx hSE w' hw' (curve l.val v) heV
  have hzero := CoefficientMarkedRecordCriticalScanTransport.zeros_on_curve hn ht ha ctx hcritical (curve l.val) (hr l) u v
  rw [hu, hv] at hzero
  exact hscanU.trans (hzero.trans hscanV.symm)

/-- The interval, branch and new native word are constructed internally.
One fresh target word preserves the entire critical scan AND all historical
cut-coefficient/coordinate signs, with both literal decoded tuples exposed. -/
theorem transport_word (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx + 1 ≤ R ctx) (hSlarge : cutoff hn ht ha ctx + 1 ≤ S ctx)
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) :
    ∃ w', ∃ hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w',
      w'.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
      (pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR false ↔
        pair ctx w' ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hS false) ∧
      ∃ z z' : Fin (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx) → ℝ,
        HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
          (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val z ∧
        HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
          (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val z' ∧
        ∀ q : CoefficientMarkedRecordFullCutQueries.Label hn ht ha ctx,
          SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx q).eval₂
            (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) z) =
          SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx q).eval₂
            (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^S ctx)) z') := by
  let a : ℝ := 2 ^ cutoff hn ht ha ctx
  let b : ℝ := max ((2 : ℝ)^R ctx) ((2 : ℝ)^S ctx) + 1
  have hu0 : a < (2 : ℝ)^R ctx := pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hRlarge)
  have hv0 : a < (2 : ℝ)^S ctx := pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hSlarge)
  let u : Ioo a b := ⟨(2 : ℝ)^R ctx, hu0, lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)⟩
  let v : Ioo a b := ⟨(2 : ℝ)^S ctx, hv0, lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)⟩
  obtain ⟨x, _, heU, w', hw', hlen, heV, hscan, hsign⟩ := transport_on_interval hn ht ha ctx hR hS
    (Nat.le_of_succ_le hRlarge) (Nat.le_of_succ_le hSlarge) (le_refl a) u u v rfl rfl w hw
  exact ⟨w', hw', hlen, hscan, x u, x v, heU, heV, hsign⟩

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutTransport
