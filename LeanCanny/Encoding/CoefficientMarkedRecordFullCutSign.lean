/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutQueries
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
/-! # Every historical cut probe on the SAME coherent full-row branches -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def packet (ctx : List Bool) := pair ctx (List.replicate (IntegralMixedCausalRecordPlanBits.count ctx) true)
theorem packet_FP : packet ∈ FP := mem_FP_pair id_mem_FP IntegralMixedCausalRecordPlanBits.count_unary.mem_FP

noncomputable def count (ctx : List Bool) :=
  (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count
theorem count_unary : UnaryFn (count hn ht ha) :=
  ((CoefficientMarkedRecordFullHeadControls.count_unary hn ht ha).comp packet_FP).of_eq (fun ctx => by
    simp only [packet, count, CoefficientMarkedRecordFullHeadControls.count,
      CoefficientMarkedRecordFullHeadControls.context, CoefficientMarkedRecordFullHeadControls.stage,
      pairFst_pair, pairSnd_pair, List.length_replicate, min_self])

noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx +
  CoefficientMarkedRecordCutCoefficientBounds.coefficientBudget hn ht ha ctx
theorem mass_binary : BinaryFn (mass hn ht ha) :=
  (CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).add
    (CoefficientMarkedRecordCutCoefficientBounds.coefficientBudget_binary hn ht ha)

noncomputable def signCutoff (ctx : List Bool) := ParameterizedGridQuerySign.cutoffBudget (count hn ht ha ctx)
  (ParameterizedGridQuerySign.commonWidth (count hn ht ha ctx) (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordFullCutQueries.spatialDegree hn ht ha ctx)) (mass hn ht ha ctx)
theorem signCutoff_binary : BinaryFn (signCutoff hn ht ha) :=
  ParameterizedGridQuerySign.commonCutoff_binary (count_unary hn ht ha)
    (CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha)
    (CoefficientMarkedRecordFullCutQueries.spatialDegree_binary hn ht ha) (mass_binary hn ht ha)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx + signCutoff hn ht ha ctx + 1
theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).add (signCutoff_binary hn ht ha)).add (BinaryFn.const 1)
theorem row_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx :=
  (Nat.le_add_right _ _).trans (Nat.le_succ _)
theorem sign_cutoff_le (ctx : List Bool) : signCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx :=
  (Nat.le_add_left _ _).trans (Nat.le_succ _)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  CoefficientMarkedRecordFullCutQueries.polynomial cutoff signCutoff mass

theorem sign_on_root_curve (ctx : List Bool) {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (query : CoefficientMarkedRecordFullCutQueries.Label hn ht ha ctx) (u v : Ioo a b) :
    SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx query).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx query).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ i, (p i).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []) 1)
  have hpm : ∀ i j, coefficientMass ((p i).coeff j) ≤ 2 ^ mass hn ht ha ctx := by
    intro i j
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i j).2.trans
        (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hqm : ∀ e, coefficientMass ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx query).coeff e) ≤ 2 ^ mass hn ht ha ctx := by
    intro e
    unfold mass
    exact (CoefficientMarkedRecordFullCutQueries.coefficient_mass hn ht ha ctx query e).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (sign_cutoff_le hn ht ha ctx)).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordFullCutQueries.spatialDegree hn ht ha ctx) (mass hn ht ha ctx) hd
    (CoefficientMarkedRecordFullCutQueries.polynomial_degree hn ht ha ctx query) hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] y.val (x y) (hx y)

/-- All historical cut-coefficient and physical coordinate signs are preserved on ONE actual finite full-row-root family;
no independently chosen family or supplied head/query model is identified. -/
theorem exists_branches (ctx : List Bool) {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a) (s : Ioo a b) :
    ∃ curve : CoefficientMarkedRecordRootBranches.Curve hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl a b s,
      Finite (CoefficientMarkedRecordRootBranches.RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve) ∧
      (∀ l : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve,
        ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (curve l.val u)) ∧
      (∀ u : Ioo a b, ∀ z, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val z ↔
        ∃! l : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve, curve l.val u = z) ∧
      (∀ l : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve,
        ∀ query, ∀ u v : Ioo a b,
        SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx query).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (curve l.val u)) =
        SignType.sign ((CoefficientMarkedRecordFullCutQueries.polynomial hn ht ha ctx query).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (curve l.val v))) := by
  have hrow : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (row_cutoff_le hn ht ha ctx)).trans ha0
  obtain ⟨curve, hf, hr, hc⟩ := CoefficientMarkedRecordRootBranches.exists_branches hn ht ha ctx
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl hrow s
  exact ⟨curve, hf, hr, hc, fun l query u v => sign_on_root_curve hn ht ha ctx ha0 (curve l.val) (hr l) query u v⟩

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutSign
