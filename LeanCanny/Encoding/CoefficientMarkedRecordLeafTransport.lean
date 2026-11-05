/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafValue
/-! # Original native leaf readers on one complete physical root branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private noncomputable def native_language (B : IntegralFramedBankQuery.Bank)
    (Q : IntegerPolynomialRootQueriesBits.Source) (N : List Bool → ℕ) :=
  IntegralFramedPhysicalIntegerLeaves.language B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    B.key B.positive Q N

private theorem count_bound_cast (B : IntegralFramedBankQuery.Bank) (c : List Bool) (N : ℕ)
    (h : N ≤ (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count) :
    N ≤ (IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (B.key c) := h

private theorem native_language_iff (B : IntegralFramedBankQuery.Bank)
    (Q : IntegerPolynomialRootQueriesBits.Source) (N : List Bool → ℕ) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (hN : N c ≤ (IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (B.key c)) :
    pair c w ∈ native_language B Q N ↔
      ∀ i < N c, CoefficientMarkedRecordLeafRecipe.reader B Q c w i = InfinitesimalSign.encode 0 := by
  simp only [native_language, IntegralFramedPhysicalIntegerLeaves.language, Set.mem_ofPred_eq,
    pairFst_pair, pairSnd_pair, hw, hN, true_and,
    IntegralFramedPhysicalIntegerLeaves.holds, IntegralFramedPhysicalIntegerLeaves.probe,
    List.length_replicate, CoefficientMarkedRecordLeafRecipe.reader]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem effective_le (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤
      CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans
    (CoefficientMarkedRecordLeafSign.row_cutoff_le hn ht ha ctx)

theorem value_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ a)
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
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v)) (i : CoefficientMarkedRecordLeafSign.Label (n := n) ctx) :
    CoefficientMarkedRecordLeafValue.value hn ht ha hR ctx w i.val =
      CoefficientMarkedRecordLeafValue.value hn ht ha hS ctx w' i.val := by
  rw [CoefficientMarkedRecordLeafValue.value_eq hn ht ha hR ctx w i
      ((effective_le hn ht ha ctx).trans hRlarge) hw (x u) hz,
    CoefficientMarkedRecordLeafValue.value_eq hn ht ha hS ctx w' i
      ((effective_le hn ht ha ctx).trans hSlarge) hw' (x v) hz']
  have h := CoefficientMarkedRecordLeafSign.sign_on_root_curve hn ht ha ctx ha0 x hx i u v
  rw [hu, hv] at h
  exact congrArg InfinitesimalSign.encode h

/-- All original leaves are read at ONE own complete tuple. The actual count
bound and packet decoder are derived internally. -/
theorem leaves_iff {R : List Bool → ℕ} (hR : BinaryFn R) (ctx w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) :
    pair ctx w ∈ IntegralMixedPhysicalMarkedTest.leaves hn ht ha hR false ↔
      ∀ i : CoefficientMarkedRecordLeafSign.Label (n := n) ctx,
        CoefficientMarkedRecordLeafValue.value hn ht ha hR ctx w i.val = InfinitesimalSign.encode 0 := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let Q := IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false
  let N := IntegralMixedPhysicalMarkedPlan.leafCount n false
  have hN : N (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ≤
      (IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth
        (B.key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) :=
    count_bound_cast B (IntegralMixedPhysicalMarkedTest.sampleContext ctx) _
      (IntegralMixedPhysicalMarkedPlan.count_bound hn ht ha hR false ctx)
  have hg := native_language_iff B Q N (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw hN
  have hCount : N (IntegralMixedPhysicalMarkedTest.sampleContext ctx) =
      IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8 := by
    simp only [N, IntegralMixedPhysicalMarkedPlan.leafCount, Bool.false_eq_true, ite_false,
      IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair]
  rw [hCount] at hg
  have hl : IntegralMixedPhysicalMarkedTest.leafQuery (pair ctx w) =
      pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w := by
    simp only [IntegralMixedPhysicalMarkedTest.leafQuery, pairFst_pair, pairSnd_pair]
  change (IntegralMixedPhysicalMarkedTest.leafQuery (pair ctx w) ∈ native_language B Q N) ↔ _
  rw [hl, hg]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

/-- The ENTIRE original integer-leaf scan uses the same two full tuples. -/
theorem leaves_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordLeafSign.cutoff hn ht ha ctx ≤ a)
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
    pair ctx w ∈ IntegralMixedPhysicalMarkedTest.leaves hn ht ha hR false ↔
      pair ctx w' ∈ IntegralMixedPhysicalMarkedTest.leaves hn ht ha hS false := by
  rw [leaves_iff hn ht ha hR ctx w hw, leaves_iff hn ht ha hS ctx w' hw']
  apply forall_congr'
  intro i
  rw [value_on_curve hn ht ha ctx hR hS hRlarge hSlarge ha0 x hx u v hu hv w w' hw hw' hz hz' i]

end LeanCanny.Encoding.CoefficientMarkedRecordLeafTransport
