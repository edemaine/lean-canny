/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutSign
/-! # Whole historical head readers agree on the same full-row branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem natural_fin {N : ℕ} (z : Fin N → ℝ) (i : Fin N) :
    CoefficientFinitePhysicalQuery.natural z i.val = z i := dite_eq_left i.isLt

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- Every stage uses the same original coordinate label, with exact native
clamping, even for padding and out-of-range stage requests. -/
theorem value_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y))
    (u v : Ioo a b) (w w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v)) (j : ℕ) :
    IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR false (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) =
      IntegralMixedPhysicalTraceCutGuards.head hn ht ha hS false (IntegralFramedTraceCutScan.stagePacket (pair ctx w') j) := by
  have hcount := (CoefficientMarkedRecordCriticalFullSemantics.full_count hn ht ha hR ctx).symm
  have hp : 0 < CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx :=
    lt_of_lt_of_eq ((IntegralMixedPhysicalMarkedTest.input hn ht ha hR false).count_pos
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) hcount
  let i : Fin (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx) :=
    ⟨min (CoefficientMarkedRecordTraceHeadQuery.column hn ht ha ctx j)
      (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx-1), by
      have hmin := Nat.min_le_right (CoefficientMarkedRecordTraceHeadQuery.column hn ht ha ctx j)
        (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx-1)
      omega⟩
  rw [CoefficientMarkedRecordTraceHeadQuery.value hn ht ha hR ctx w j hw (x u) hz,
    CoefficientMarkedRecordTraceHeadQuery.value hn ht ha hS ctx w' j hw' (x v) hz']
  change InfinitesimalSign.encode (SignType.sign (CoefficientFinitePhysicalQuery.natural (x u) i.val)) =
    InfinitesimalSign.encode (SignType.sign (CoefficientFinitePhysicalQuery.natural (x v) i.val))
  rw [natural_fin, natural_fin]
  have h := CoefficientMarkedRecordFullCutSign.sign_on_root_curve hn ht ha ctx ha0 x hx (.inl i) u v
  simp only [CoefficientMarkedRecordFullCutQueries.polynomial, MvPolynomial.eval₂_X] at h
  exact congrArg InfinitesimalSign.encode h

end LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadSign
