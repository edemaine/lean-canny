/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullHeadControls
public import LeanCanny.Encoding.CoefficientMarkedRecordRowDegree
public import LeanCanny.Geometry.ParameterizedCartesianBranches
/-! # Actual full-column Cartesian branches preserve the actual row equations

Heads, queries, degrees, masses and the common prefix cutoff are constructed
from original syntax. The preserved queries include every literal full row.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCartesianRows
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def headDegree (ctx : List Bool) := CoefficientMarkedRecordFullHeadControls.budget hn ht ha ctx + 1
noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordFullHeadControls.coefficientBudget hn ht ha ctx +
  CoefficientMarkedRecordRowBounds.coefficientBudget hn ht ha ctx

theorem headDegree_binary : BinaryFn (headDegree hn ht ha) :=
  (CoefficientMarkedRecordFullHeadControls.budget_binary hn ht ha).add (BinaryFn.const 1)
theorem mass_binary : BinaryFn (mass hn ht ha) :=
  (CoefficientMarkedRecordFullHeadControls.coefficientBudget_binary hn ht ha).add
    (CoefficientMarkedRecordRowBounds.coefficientBudget_binary hn ht ha)

noncomputable def prefixCutoff (q : List Bool) :=
  ParameterizedCartesianBranches.cutoff (CoefficientMarkedRecordFullHeadControls.count hn ht ha q)
    (headDegree hn ht ha (CoefficientMarkedRecordFullHeadControls.context q))
    (CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha (CoefficientMarkedRecordFullHeadControls.context q))
    (mass hn ht ha (CoefficientMarkedRecordFullHeadControls.context q))

theorem prefixCutoff_binary : BinaryFn (prefixCutoff hn ht ha) :=
  ParameterizedCartesianBranches.cutoff_binary (CoefficientMarkedRecordFullHeadControls.count_unary hn ht ha)
    ((headDegree_binary hn ht ha).comp CoefficientMarkedRecordFullHeadControls.context_FP)
    ((CoefficientMarkedRecordRowDegree.spatialDegree_binary hn ht ha).comp CoefficientMarkedRecordFullHeadControls.context_FP)
    ((mass_binary hn ht ha).comp CoefficientMarkedRecordFullHeadControls.context_FP)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx +
  (∑ k ∈ Finset.range (IntegralMixedCausalRecordPlanBits.count ctx + 1), prefixCutoff hn ht ha (pair ctx (List.replicate k true))) + 1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).add
    (BinaryFn.sum (IntegralMixedCausalRecordPlanBits.count_unary.add (UnaryFn.const 1))
      (prefixCutoff_binary hn ht ha))).add (BinaryFn.const 1)

theorem effectiveCutoff_le (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

theorem cartesian_cutoff_le (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    ParameterizedCartesianBranches.cutoff (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count
      (headDegree hn ht ha ctx) (CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx) (mass hn ht ha ctx) ≤
      cutoff hn ht ha ctx := by
  have he : prefixCutoff hn ht ha (pair ctx (List.replicate k true)) =
      ParameterizedCartesianBranches.cutoff (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count
        (headDegree hn ht ha ctx) (CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx) (mass hn ht ha ctx) := by
    simp only [prefixCutoff, CoefficientMarkedRecordFullHeadControls.count,
      CoefficientMarkedRecordFullHeadControls.context, CoefficientMarkedRecordFullHeadControls.stage,
      pairFst_pair, pairSnd_pair, List.length_replicate, min_eq_left hk]
  rw [← he]
  have hh : prefixCutoff hn ht ha (pair ctx (List.replicate k true)) ≤
      ∑ j ∈ Finset.range (IntegralMixedCausalRecordPlanBits.count ctx + 1),
        prefixCutoff hn ht ha (pair ctx (List.replicate j true)) :=
    Finset.single_le_sum (f := fun j : ℕ => prefixCutoff hn ht ha (pair ctx (List.replicate j true)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  unfold cutoff
  exact hh.trans ((Nat.le_add_left _ _).trans (Nat.le_succ _))

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  headDegree mass cutoff

/-- Actual constructed heads cover their full Cartesian grid, while EVERY actual
symbolic row stays zero exactly on the same branches throughout the interval. -/
theorem exists_branches (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    {a b : ℝ} (ha0 : (2 : ℝ) ^ cutoff hn ht ha ctx ≤ a) (s : Ioo a b) :
    let F := CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk
    let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk []
    ∃ curve : ParameterizedCartesianBranches.Index p a b s → C(Ioo a b, Fin F.count → ℝ),
      (∀ l u i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (curve l u i) = 0) ∧
      (∀ u : Ioo a b, ∀ z : Fin F.count → ℝ,
        (∀ i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (z i) = 0) ↔ ∃! l, curve l u = z) ∧
      (∀ l u v,
        (∀ i, (F.rows i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (curve l u) = 0) ↔
        (∀ i, (F.rows i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (curve l v) = 0)) := by
  dsimp only
  let F := CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk []
  have hp : ∀ i, 0 < (p i).natDegree := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx k hk []
  have hd : ∀ i, (p i).natDegree ≤ headDegree hn ht ha ctx := by
    unfold headDegree
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx k hk [] i).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx k hk []) 1)
  have hpm : ∀ i j, coefficientMass ((p i).coeff j) ≤ 2 ^ mass hn ht ha ctx := by
    intro i j
    unfold mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx k hk [] i j).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hqm : ∀ i e, coefficientMass ((F.rows i).coeff e) ≤ 2 ^ mass hn ht ha ctx := by
    intro i e
    unfold mass
    exact (CoefficientMarkedRecordRowBounds.coefficient_degree_mass hn ht ha ctx k hk i e).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ) ^ ParameterizedCartesianBranches.cutoff F.count (headDegree hn ht ha ctx)
      (CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx) (mass hn ht ha ctx) ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (cartesian_cutoff_le hn ht ha ctx k hk)).trans ha0
  obtain ⟨curve, _, hroot, hcover, _, hsign⟩ := ParameterizedCartesianBranches.exists_branches p F.rows
    (headDegree hn ht ha ctx) (CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx) (mass hn ht ha ctx)
    hp hd (CoefficientMarkedRecordRowDegree.row_degree hn ht ha ctx k hk) hpm hqm hstart s
  refine ⟨curve, hroot, hcover, ?_⟩
  intro l u v
  constructor
  · intro hu i
    exact sign_eq_zero_iff.mp ((hsign l i u v).symm.trans (sign_eq_zero_iff.mpr (hu i)))
  · intro hv i
    exact sign_eq_zero_iff.mp ((hsign l i u v).trans (sign_eq_zero_iff.mpr (hv i)))

end LeanCanny.Encoding.CoefficientMarkedRecordCartesianRows
