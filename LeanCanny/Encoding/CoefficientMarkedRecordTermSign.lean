/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
/-! # Every original bank-term test on the SAME coherent full-row branches -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermSign
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

noncomputable def polynomial (word : List Bool → List Bool) (ctx : List Bool) :
    MvPolynomial (Fin (count hn ht ha ctx)) ℤ[X] :=
  CoefficientMarkedRecordTermQuery.polynomial hn ht ha word ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl

theorem polynomial_degree (word : List Bool → List Bool) (ctx : List Bool) :
    (polynomial hn ht ha word ctx).totalDegree ≤ CoefficientMarkedRecordTermQuery.spatialDegree hn ht ha word ctx :=
  CoefficientMarkedRecordTermQuery.polynomial_spatial_degree hn ht ha word ctx _ le_rfl

theorem coefficient_mass (word : List Bool → List Bool) (ctx : List Bool) (e : Fin (count hn ht ha ctx) →₀ ℕ) :
    coefficientMass ((polynomial hn ht ha word ctx).coeff e) ≤
      2^CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha word ctx :=
  (CoefficientMarkedRecordTermQuery.coefficient_degree_mass hn ht ha word ctx _ le_rfl e).2

variable (word : List Bool → List Bool) (hw : word ∈ FP)

noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx +
  CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha word ctx
include hw in
theorem mass_binary : BinaryFn (mass hn ht ha word) :=
  (CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).add
    (CoefficientMarkedRecordTermQuery.coefficientBudget_binary hn ht ha word hw)

noncomputable def signCutoff (ctx : List Bool) := ParameterizedGridQuerySign.cutoffBudget (count hn ht ha ctx)
  (ParameterizedGridQuerySign.commonWidth (count hn ht ha ctx) (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordTermQuery.spatialDegree hn ht ha word ctx)) (mass hn ht ha word ctx)
include hw in
theorem signCutoff_binary : BinaryFn (signCutoff hn ht ha word) :=
  ParameterizedGridQuerySign.commonCutoff_binary (count_unary hn ht ha)
    (CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha)
    (CoefficientMarkedRecordTermQuery.spatialDegree_binary hn ht ha word hw) (mass_binary hn ht ha word hw)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx + signCutoff hn ht ha word ctx + 1
include hw in
theorem cutoff_binary : BinaryFn (cutoff hn ht ha word) :=
  ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).add (signCutoff_binary hn ht ha word hw)).add (BinaryFn.const 1)
theorem row_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ cutoff hn ht ha word ctx :=
  (Nat.le_add_right _ _).trans (Nat.le_succ _)
theorem sign_cutoff_le (ctx : List Bool) : signCutoff hn ht ha word ctx ≤ cutoff hn ht ha word ctx :=
  (Nat.le_add_left _ _).trans (Nat.le_succ _)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  polynomial cutoff signCutoff mass

theorem sign_on_root_curve (ctx : List Bool) {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha word ctx ≤ a)
    (x : C(Ioo a b, Fin (count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (u v : Ioo a b) :
    SignType.sign ((polynomial hn ht ha word ctx).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((polynomial hn ht ha word ctx).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ i, (p i).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []) 1)
  have hpm : ∀ i j, coefficientMass ((p i).coeff j) ≤ 2 ^ mass hn ht ha word ctx := by
    intro i j
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i j).2.trans
        (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hqm : ∀ e, coefficientMass ((polynomial hn ht ha word ctx).coeff e) ≤ 2 ^ mass hn ht ha word ctx := by
    intro e
    unfold mass
    exact (coefficient_mass hn ht ha word ctx e).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha word ctx ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (sign_cutoff_le hn ht ha word ctx)).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordTermQuery.spatialDegree hn ht ha word ctx) (mass hn ht ha word ctx) hd
    (polynomial_degree hn ht ha word ctx) hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] y.val (x y) (hx y)


end LeanCanny.Encoding.CoefficientMarkedRecordTermSign
