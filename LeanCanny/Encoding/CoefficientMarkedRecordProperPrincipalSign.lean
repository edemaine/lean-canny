/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSpatial
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSeries
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
/-! # Actual ordinary/mean principal coefficient signs on full-row curves -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry Polynomial Set
open IntegralMixedRoadmapProperRow
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

structure Label (z : List Bool) where
  nonempty : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)
  row : rankRowSyntax n z
  power : Fin 3
  eta : Bool
  epsilon : Bool
  principal : ℕ
  delta : ℕ
  inner : ℕ

noncomputable def count (mean : Bool) (z : List Bool) := (properPhysicalData hn ht ha mean z).count

noncomputable def naturalPolynomial (mean right : Bool) (z : List Bool) (q : Label (n := n) z) :
    MvPolynomial ℕ ℤ[X] := if mean then
  properRankPhysical hn ht ha q.power q.epsilon z q.nonempty q.principal q.delta q.inner else
  properNearPhysical hn ht ha right q.power q.eta q.epsilon z q.nonempty q.principal q.delta q.inner

theorem variable_bound (mean right : Bool) (z : List Bool) (q : Label (n := n) z) :
    ∀ i ∈ (naturalPolynomial hn ht ha mean right z q).vars, i < count hn ht ha mean z := by
  intro i hi
  cases mean
  · exact Finset.mem_range.mp (proper_near_variable_box hn ht ha right q.power q.eta q.epsilon z q.nonempty
      q.principal q.delta q.inner hi)
  · exact Finset.mem_range.mp (proper_rank_variable_box hn ht ha q.power q.epsilon z q.nonempty
      q.principal q.delta q.inner hi)

noncomputable def polynomial (mean right : Bool) (z : List Bool) (q : Label (n := n) z) :=
  CoefficientFinitePhysicalQuery.polynomial (count hn ht ha mean z) (naturalPolynomial hn ht ha mean right z q)
    (variable_bound hn ht ha mean right z q)

noncomputable def spatialDegree (mean right : Bool) :=
  if mean then properRankSpatialDegree hn ht ha else properNearSpatialDegree hn ht ha right
noncomputable def coefficientBudget (mean : Bool) :=
  if mean then properRankCoefficientBudget hn ht ha else properNearCoefficientBudget hn ht ha
noncomputable def mass (mean : Bool) (z : List Bool) :=
  CoefficientMarkedRecordCartesianRows.mass hn ht ha (catalogRoot n mean z) + coefficientBudget hn ht ha mean z
noncomputable def signCutoff (mean right : Bool) (z : List Bool) :=
  ParameterizedGridQuerySign.cutoffBudget (count hn ht ha mean z)
    (ParameterizedGridQuerySign.commonWidth (count hn ht ha mean z)
      (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha (catalogRoot n mean z))
      (spatialDegree hn ht ha mean right z)) (mass hn ht ha mean z)
noncomputable def cutoff (mean right : Bool) (z : List Bool) :=
  CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (catalogRoot n mean z) + signCutoff hn ht ha mean right z + 1

include hn ht ha in
private theorem root_FP (mean : Bool) : catalogRoot n mean ∈ FP := by
  cases mean
  · exact near_catalogRoot_FP hn ht ha
  · exact rank_catalogRoot_FP hn ht ha

theorem cutoff_binary (mean right : Bool) : BinaryFn (cutoff hn ht ha mean right) := by
  have HS : BinaryFn (spatialDegree hn ht ha mean right) := by
    cases mean
    · exact properNearSpatialDegree_binary hn ht ha right
    · exact properRankSpatialDegree_binary hn ht ha
  have HB : BinaryFn (coefficientBudget hn ht ha mean) := by
    cases mean
    · exact properNearCoefficientBudget_binary hn ht ha
    · exact properRankCoefficientBudget_binary hn ht ha
  have HM : BinaryFn (mass hn ht ha mean) :=
    BinaryFn.add ((CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).comp (root_FP hn ht ha mean)) HB
  have HC : BinaryFn (signCutoff hn ht ha mean right) :=
    ParameterizedGridQuerySign.commonCutoff_binary (proper_physical_count_unary hn ht ha mean)
      ((CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha).comp (root_FP hn ht ha mean)) HS HM
  exact BinaryFn.add (BinaryFn.add
    ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).comp (root_FP hn ht ha mean)) HC) (BinaryFn.const 1)

theorem effective_le (mean right : Bool) (z : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      cutoff hn ht ha mean right z :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha (catalogRoot n mean z)).trans
    ((Nat.le_add_right _ _).trans (Nat.le_succ _))

theorem degree (mean right : Bool) (z : List Bool) (q : Label (n := n) z) :
    (polynomial hn ht ha mean right z q).totalDegree ≤ spatialDegree hn ht ha mean right z := by
  rw [polynomial, CoefficientFinitePhysicalQuery.degree_eq]
  cases mean
  · exact proper_near_spatial_degree hn ht ha right q.power q.eta q.epsilon z q.nonempty q.row q.principal q.delta q.inner
  · exact proper_rank_spatial_degree hn ht ha q.power q.epsilon z q.nonempty q.row q.principal q.delta q.inner

theorem coefficient_mass (mean right : Bool) (z : List Bool) (q : Label (n := n) z)
    (e : Fin (count hn ht ha mean z) →₀ ℕ) :
    coefficientMass ((polynomial hn ht ha mean right z q).coeff e) ≤ 2 ^ coefficientBudget hn ht ha mean z := by
  rw [polynomial, CoefficientFinitePhysicalQuery.coefficient]
  cases mean
  · exact (proper_near_coefficient_degree_mass hn ht ha right q.power q.eta q.epsilon z q.nonempty q.row
      q.principal q.delta q.inner _).2
  · exact (proper_rank_coefficient_degree_mass hn ht ha q.power q.epsilon z q.nonempty q.row
      q.principal q.delta q.inner _).2

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  polynomial cutoff signCutoff mass

/-- All principal indices and both infinitesimal coefficient layers share one
original cutoff. The curve is an actual full-row root curve at the literal
ordinary or mean prepared root. -/
theorem sign_on_root_curve (mean right : Bool) (z : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha mean right z ≤ a)
    (x : C(Ioo a b, Fin (count hn ht ha mean z) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n mean z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n mean z)) le_rfl u.val (x u))
    (q : Label (n := n) z) (u v : Ioo a b) :
    SignType.sign ((polynomial hn ht ha mean right z q).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
      SignType.sign ((polynomial hn ht ha mean right z q).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let ctx := catalogRoot n mean z
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ i, (p i).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx)
      le_rfl [] i).trans (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []) 1)
  have hpm : ∀ i j, coefficientMass ((p i).coeff j) ≤ 2^mass hn ht ha mean z := by
    intro i j
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i j).2.trans
      (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hqm : ∀ e, coefficientMass ((polynomial hn ht ha mean right z q).coeff e) ≤ 2^mass hn ht ha mean z := by
    intro e
    unfold mass
    exact (coefficient_mass hn ht ha mean right z q e).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha mean right z ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show signCutoff hn ht ha mean right z ≤ cutoff hn ht ha mean right z by
        unfold cutoff
        exact (Nat.le_add_left _ _).trans (Nat.le_succ _))).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha mean right z)
    (mass hn ht ha mean z) hd (degree hn ht ha mean right z q) hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx)
    le_rfl [] y.val (x y) (hx y)

end LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSign
