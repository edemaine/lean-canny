/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
/-! # Full-cut principal signs on one actual complete physical root curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipalSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
structure Label (ctx : List Bool) where
  stage : ℕ
  stage_lt : stage < IntegralMixedCausalRecordPlanBits.count ctx
  is_cut : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx stage) = false
  endpoint : ℕ
  negative : Bool
  principal : ℕ
  delta : ℕ
  epsilon : ℕ

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
noncomputable def count (ctx : List Bool) := (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count
noncomputable def polynomial (ctx : List Bool) (q : Label ctx) :=
  CoefficientMarkedRecordFullCutBounds.finite hn ht ha ctx q.stage q.stage_lt q.endpoint q.negative q.principal q.delta q.epsilon
noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx+
  CoefficientMarkedRecordFullCutBounds.coefficientBudget hn ht ha ctx
noncomputable def signCutoff (ctx : List Bool) := ParameterizedGridQuerySign.cutoffBudget (count hn ht ha ctx)
  (ParameterizedGridQuerySign.commonWidth (count hn ht ha ctx) (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordFullCutBounds.spatialDegree hn ht ha ctx)) (mass hn ht ha ctx)
noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx+signCutoff hn ht ha ctx+1

theorem signCutoff_binary : BinaryFn (signCutoff hn ht ha) :=
  ParameterizedGridQuerySign.commonCutoff_binary (CoefficientMarkedRecordFullCutPhysical.count_unary hn ht ha)
    (CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha)
    (CoefficientMarkedRecordFullCutBounds.spatialDegree_binary hn ht ha)
    ((CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).add
      (CoefficientMarkedRecordFullCutBounds.coefficientBudget_binary hn ht ha))
theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).add (signCutoff_binary hn ht ha)).add (BinaryFn.const 1)

theorem row_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx :=
  (Nat.le_add_right _ _).trans (Nat.le_succ _)
theorem sign_cutoff_le (ctx : List Bool) : signCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx :=
  (Nat.le_add_left _ _).trans (Nat.le_succ _)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  CoefficientMarkedRecordFullCutBounds.finite cutoff signCutoff mass

/-- Every principal slice, including zero/repeated-root degeneracies, keeps
its sign on the same actual full-row curve. No independent root choices or
constant sampler ordinals are used. -/
theorem sign_on_root_curve (ctx : List Bool) {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (q : Label ctx) (u v : Ioo a b) :
    SignType.sign ((polynomial hn ht ha ctx q).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((polynomial hn ht ha ctx q).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
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
  have hqm : ∀ e, coefficientMass ((polynomial hn ht ha ctx q).coeff e) ≤ 2^mass hn ht ha ctx := by
    intro e
    unfold mass
    exact (CoefficientMarkedRecordFullCutBounds.finite_coefficient_degree_mass hn ht ha ctx q.stage q.stage_lt
      q.is_cut q.endpoint q.negative q.principal q.delta q.epsilon e).2.trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (sign_cutoff_le hn ht ha ctx)).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordFullCutBounds.spatialDegree hn ht ha ctx) (mass hn ht ha ctx) hd
    (CoefficientMarkedRecordFullCutBounds.finite_degree hn ht ha ctx q.stage q.stage_lt q.endpoint q.negative q.principal q.delta q.epsilon)
    hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] y.val (x y) (hx y)

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipalSign
