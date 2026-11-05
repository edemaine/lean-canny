/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalBranchSign
/-! # Both actual critical interval signs on the same full raw-root curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalIntervalSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def spatialDegree (ctx : List Bool) :=
  CoefficientMarkedRecordTermQuery.spatialDegree hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false false) ctx +
    CoefficientMarkedRecordTermQuery.spatialDegree hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false true) ctx

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) :=
  (CoefficientMarkedRecordTermQuery.spatialDegree_binary hn ht ha _
    (IntegralMixedPhysicalCriticalInterval.word_FP hn false false)).add
    (CoefficientMarkedRecordTermQuery.spatialDegree_binary hn ht ha _
      (IntegralMixedPhysicalCriticalInterval.word_FP hn false true))

theorem query_degree (upper : Bool) (ctx : List Bool) :
    (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper ctx).totalDegree ≤ spatialDegree hn ht ha ctx := by
  have hh := CoefficientMarkedRecordTermQuery.polynomial_spatial_degree hn ht ha
    (IntegralMixedPhysicalCriticalInterval.word n false upper) ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl
  cases upper
  · exact hh.trans (Nat.le_add_right _ _)
  · exact hh.trans (Nat.le_add_left _ _)

noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx +
  CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false false) ctx +
    CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false true) ctx

theorem mass_binary : BinaryFn (mass hn ht ha) :=
  ((CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).add
    (CoefficientMarkedCriticalIntervalQuery.budget_binary hn ht ha false)).add
    (CoefficientMarkedCriticalIntervalQuery.budget_binary hn ht ha true)

private theorem head_mass_le (ctx : List Bool) :
    CoefficientMarkedRecordFullHeadControls.coefficientBudget hn ht ha ctx ≤ mass hn ht ha ctx := by
  unfold mass CoefficientMarkedRecordCartesianRows.mass
  omega

private theorem query_mass_le (upper : Bool) (ctx : List Bool) :
    CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false upper) ctx ≤
      mass hn ht ha ctx := by
  cases upper <;> unfold mass <;> omega

noncomputable def signCutoff (ctx : List Bool) :=
  ParameterizedGridQuerySign.cutoffBudget (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx)
    (ParameterizedGridQuerySign.commonWidth (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx)
      (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha ctx)) (mass hn ht ha ctx)

theorem signCutoff_binary : BinaryFn (signCutoff hn ht ha) :=
  ParameterizedGridQuerySign.commonCutoff_binary (CoefficientMarkedRecordCriticalBranchSign.count_unary hn ht ha)
    (CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha) (spatialDegree_binary hn ht ha) (mass_binary hn ht ha)

noncomputable def cutoff (ctx : List Bool) :=
  CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx + signCutoff hn ht ha ctx + 1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).add (signCutoff_binary hn ht ha)).add (BinaryFn.const 1)

theorem row_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

theorem sign_cutoff_le (ctx : List Bool) : signCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  CoefficientMarkedCriticalIntervalQuery.polynomial cutoff signCutoff mass

/-- The two literal endpoint inequalities are preserved on ANY actual full
row-root curve. Heads, query recipes and original bounds are all constructed. -/
theorem sign_on_root_curve (upper : Bool) (ctx : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (u v : Ioo a b) :
    SignType.sign ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper ctx).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper ctx).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ j, (p j).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro j
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx _ le_rfl [] j).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx _ le_rfl []) 1)
  have hpm : ∀ j l, coefficientMass ((p j).coeff l) ≤ 2 ^ mass hn ht ha ctx := by
    intro j l
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx _ le_rfl [] j l).2.trans
      (Nat.pow_le_pow_right (by decide) (head_mass_le hn ht ha ctx))
  have hqm : ∀ e, coefficientMass ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper ctx).coeff e) ≤
      2 ^ mass hn ht ha ctx := by
    intro e
    have hh := (CoefficientMarkedCriticalIntervalQuery.coefficient_degree_mass hn ht ha upper ctx e).2
    exact hh.trans (Nat.pow_le_pow_right (by decide) (query_mass_le hn ht ha upper ctx))
  have hstart : (2 : ℝ)^signCutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (sign_cutoff_le hn ht ha ctx)).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha ctx) (mass hn ht ha ctx)
    hd (query_degree hn ht ha upper ctx) hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx _ le_rfl [] y.val (x y) (hx y)

end LeanCanny.Encoding.CoefficientMarkedCriticalIntervalSign
