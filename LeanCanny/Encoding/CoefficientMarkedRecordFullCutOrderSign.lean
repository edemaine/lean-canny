/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutComparison
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Literal native endpoint order is preserved on any actual full-row curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def polynomial (ctx : List Bool) (left right : ℕ) :=
  CoefficientFinitePhysicalQuery.polynomial (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count
    (CoefficientMarkedRecordFullCutOrderQuery.polynomial hn ht ha ctx left right)
    (CoefficientMarkedRecordFullCutOrderQuery.variable_box hn ht ha ctx left right)

noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx+
  (CoefficientMarkedRecordFullCutOrderQuery.productBudget hn ht ha ctx+1)

theorem mass_binary : BinaryFn (mass hn ht ha) := (CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).add
  ((CoefficientMarkedRecordFullCutOrderQuery.productBudget_binary hn ht ha).add (BinaryFn.const 1))

noncomputable def signCutoff (ctx : List Bool) := ParameterizedGridQuerySign.cutoffBudget
  (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count
  (ParameterizedGridQuerySign.commonWidth (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx))
  (mass hn ht ha ctx)

theorem signCutoff_binary : BinaryFn (signCutoff hn ht ha) := ParameterizedGridQuerySign.commonCutoff_binary
  (CoefficientMarkedRecordFullCutPhysical.count_unary hn ht ha) (CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha)
  (CoefficientMarkedRecordTermQuery.spatialPowerBound_binary hn ht ha) (mass_binary hn ht ha)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx+
  CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx+signCutoff hn ht ha ctx+1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  (((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).add
    (CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha)).add (signCutoff_binary hn ht ha)).add (BinaryFn.const 1)

theorem effective_le (ctx : List Bool) : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

theorem sign_cutoff_le (ctx : List Bool) : signCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  polynomial mass cutoff signCutoff

/-- The single original cutoff covers ALL endpoint indices. Both zero
extensions and coincident endpoint monomials are included. -/
theorem sign_on_root_curve (ctx : List Bool) (left right : ℕ) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (u v : Ioo a b) :
    SignType.sign ((CoefficientMarkedRecordFullCutOrderQuery.polynomial hn ht ha ctx left right).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation u.val) (CoefficientFinitePhysicalQuery.natural (x u))) =
    SignType.sign ((CoefficientMarkedRecordFullCutOrderQuery.polynomial hn ht ha ctx left right).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation v.val) (CoefficientFinitePhysicalQuery.natural (x v))) := by
  let p : Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → Polynomial (Polynomial ℤ) := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ i, (p i).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []) 1)
  have hpm : ∀ i j, coefficientMass ((p i).coeff j) ≤ 2^mass hn ht ha ctx := by
    intro i j
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i j).2.trans
        (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hqd : (polynomial hn ht ha ctx left right).totalDegree ≤ CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx := by
    unfold polynomial
    rw [CoefficientFinitePhysicalQuery.degree_eq]
    exact CoefficientMarkedRecordFullCutOrderQuery.spatial_degree hn ht ha ctx left right
  have hqm : ∀ e, coefficientMass ((polynomial hn ht ha ctx left right).coeff e) ≤ 2^mass hn ht ha ctx := by
    intro e
    unfold polynomial
    rw [CoefficientFinitePhysicalQuery.coefficient]
    unfold mass
    exact (CoefficientMarkedRecordFullCutOrderQuery.coefficient_degree_mass hn ht ha ctx left right _).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (sign_cutoff_le hn ht ha ctx)).trans ha0
  unfold signCutoff at hstart
  have H := ParameterizedGridQuerySign.sign_after_common_input_bounds p (polynomial hn ht ha ctx left right) hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx)
    (mass hn ht ha ctx) hd hqd hpm hqm hstart x
    (fun y => CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] y.val (x y) (hx y)) u v
  unfold polynomial at H
  rw [CoefficientFinitePhysicalQuery.evaluation, CoefficientFinitePhysicalQuery.evaluation] at H
  exact H

variable {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)

/-- Actual native order values agree for independently sampled OWN words on
the same full-row curve, with arbitrary literal radius/resource readers. -/
theorem value_on_curve (ctx : List Bool) (k left right : ℕ)
    (hRc : cutoff hn ht ha ctx ≤ R ctx) (hSc : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx) (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS hwS).val (x v)) :
    IntegralMixedPhysicalCutOrderedInterval.order hn ht ha hR false (pair (CTX ctx k left right) wR) =
      IntegralMixedPhysicalCutOrderedInterval.order hn ht ha hS false (pair (CTX ctx k left right) wS) := by
  have HR := CoefficientMarkedRecordFullCutOrderQuery.value_eq hn ht ha hR ctx k left right
    ((effective_le hn ht ha ctx).trans hRc) wR hwR (x u) hjR
  have HS := CoefficientMarkedRecordFullCutOrderQuery.value_eq hn ht ha hS ctx k left right
    ((effective_le hn ht ha ctx).trans hSc) wS hwS (x v) hjS
  have HC := sign_on_root_curve hn ht ha ctx left right ha0 x hx u v
  rw [hu, hv] at HC
  exact HR.trans ((congrArg InfinitesimalSign.encode HC).trans HS.symm)

/-- The exact sampleContext words produced by the actual root sampler suffice;
SAME-root AUX conversion is derived at each radius. -/
theorem value_on_sampled_curve (ctx : List Bool) (k left right : ℕ)
    (hRc : cutoff hn ht ha ctx ≤ R ctx) (hSc : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx) (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wS hwS).val (x v)) :
    IntegralMixedPhysicalCutOrderedInterval.order hn ht ha hR false (pair (CTX ctx k left right) wR) =
      IntegralMixedPhysicalCutOrderedInterval.order hn ht ha hS false (pair (CTX ctx k left right) wS) := by
  have hroot : pairFst (CTX ctx k left right) = pairFst (IntegralMixedPhysicalMarkedTest.sampleContext ctx) :=
    (CoefficientMarkedRecordFullCutInstalled.context_root (n := n) ctx k left right).trans (pairFst_pair ctx []).symm
  let hRctx := (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hR
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (CTX ctx k left right) wR hroot.symm).mp hwR
  let hSctx := (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hS
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (CTX ctx k left right) wS hroot.symm).mp hwS
  have hJR := (CoefficientMarkedRecordFullCutComparison.candidate_context hn ht ha hR (CTX ctx k left right)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wR hroot hRctx hwR).trans hjR
  have hJS := (CoefficientMarkedRecordFullCutComparison.candidate_context hn ht ha hS (CTX ctx k left right)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wS hroot hSctx hwS).trans hjS
  exact value_on_curve hn ht ha hR hS ctx k left right hRc hSc ha0 x hx u v hu hv wR wS hRctx hSctx hJR hJS

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderSign
