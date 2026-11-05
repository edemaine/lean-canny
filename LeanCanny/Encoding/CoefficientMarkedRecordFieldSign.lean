/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldVariables
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
/-! # Original cutoffs for literal default Field queries on actual row curves -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem power_le (right : Bool) (z : List Bool) :
    IntegralMixedPhysicalFieldEquality.catalogPower hn ht ha right z ≤
      CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z) := by
  let ctx := CoefficientMarkedRecordFieldQuery.rightRoot right z
  have hb : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ≤ CoefficientMarkedRecordActual.horizon hn ht ha ctx := by
    change IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+IntegralMixedCausalRecordPlanBits.count ctx ≤
      IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+IntegralMixedCausalRecordPlanBits.count ctx+2+1
    omega
  apply UniformIntegralPowerSchedule.birth_le
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hb)

noncomputable def spatialDegree (right : Bool) (z : List Bool) :=
  (2*IntegralMixedPhysicalFieldEquality.catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z))*
    CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)

theorem spatialDegree_binary (right : Bool) : BinaryFn (spatialDegree hn ht ha right) := by
  have HR : BinaryFn (fun z => CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha
      (CoefficientMarkedRecordFieldQuery.rightRoot right z)) :=
    (CoefficientMarkedRecordTermQuery.spatialPowerBound_binary hn ht ha).comp (CoefficientMarkedRecordFieldQuery.rightRoot_FP right)
  exact ((BinaryFn.const 2).mul ((IntegralMixedPhysicalFieldEquality.catalogDegree_binary hn ht ha).comp
    CoefficientMarkedRecordFieldSource.root_FP)).mul HR

theorem query_degree (right : Bool) (z : List Bool) (k : ℕ) :
    (CoefficientMarkedRecordFieldVariables.polynomial hn ht ha right z k).totalDegree ≤ spatialDegree hn ht ha right z :=
  (CoefficientMarkedRecordFieldVariables.degree hn ht ha right z k).trans
    (Nat.mul_le_mul_left _ (power_le hn ht ha right z))

noncomputable def mass (right : Bool) (z : List Bool) :=
  CoefficientMarkedRecordCartesianRows.mass hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)+
    CoefficientMarkedRecordFieldQuery.coefficientBudget hn ht ha right z

theorem mass_binary (right : Bool) : BinaryFn (mass hn ht ha right) :=
  BinaryFn.add ((CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).comp
    (CoefficientMarkedRecordFieldQuery.rightRoot_FP right)) (CoefficientMarkedRecordFieldQuery.coefficientBudget_binary hn ht ha right)

noncomputable def signCutoff (right : Bool) (z : List Bool) :=
  ParameterizedGridQuerySign.cutoffBudget (CoefficientMarkedRecordFieldVariables.count hn ht ha right z)
    (ParameterizedGridQuerySign.commonWidth (CoefficientMarkedRecordFieldVariables.count hn ht ha right z)
      (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z))
      (spatialDegree hn ht ha right z)) (mass hn ht ha right z)

theorem signCutoff_binary (right : Bool) : BinaryFn (signCutoff hn ht ha right) :=
  ParameterizedGridQuerySign.commonCutoff_binary (CoefficientMarkedRecordFieldVariables.count_unary hn ht ha right)
    ((CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha).comp (CoefficientMarkedRecordFieldQuery.rightRoot_FP right))
    (spatialDegree_binary hn ht ha right) (mass_binary hn ht ha right)

noncomputable def cutoff (right : Bool) (z : List Bool) :=
  CoefficientMarkedRecordFieldQuery.cutoff hn ht ha right z+
    CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)+
      signCutoff hn ht ha right z+1

theorem cutoff_binary (right : Bool) : BinaryFn (cutoff hn ht ha right) :=
  (((CoefficientMarkedRecordFieldQuery.cutoff_binary hn ht ha right).add
    ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).comp (CoefficientMarkedRecordFieldQuery.rightRoot_FP right))).add
    (signCutoff_binary hn ht ha right)).add (BinaryFn.const 1)

theorem sign_cutoff_le (right : Bool) (z : List Bool) : signCutoff hn ht ha right z ≤ cutoff hn ht ha right z := by
  unfold cutoff
  omega
theorem row_cutoff_le (right : Bool) (z : List Bool) :
    CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z) ≤ cutoff hn ht ha right z := by
  unfold cutoff
  omega
theorem query_cutoff_le (right : Bool) (z : List Bool) :
    CoefficientMarkedRecordFieldQuery.cutoff hn ht ha right z ≤ cutoff hn ht ha right z := by
  unfold cutoff
  omega

/-- The ceiling is independent of derivative orders, retained labels and
sampled words: its two root addresses determine every numeric input. -/
theorem cutoff_roots (right : Bool) (z z' : List Bool)
    (hL : CoefficientMarkedRecordFieldSource.root z = CoefficientMarkedRecordFieldSource.root z')
    (hR : CoefficientMarkedRecordFieldQuery.rightRoot right z = CoefficientMarkedRecordFieldQuery.rightRoot right z') :
    cutoff hn ht ha right z = cutoff hn ht ha right z' := by
  unfold cutoff signCutoff mass spatialDegree CoefficientMarkedRecordFieldVariables.count
  simp only [CoefficientMarkedRecordFieldQuery.coefficientBudget, CoefficientMarkedRecordFieldQuery.cutoff,
    CoefficientMarkedRecordFieldQuery.slope, CoefficientMarkedRecordFieldQuery.offset, hL, hR]

theorem cutoff_packet (right : Bool) (cL cR wL wR : List Bool) (a b : ℕ) :
    cutoff hn ht ha right (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) =
      cutoff hn ht ha right (IntegralMixedPhysicalFieldEquality.packet cL [] cR [] 0 0) := by
  apply cutoff_roots
  · simp only [CoefficientMarkedRecordFieldSource.root, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet,
      Bool.false_eq_true, ite_false, pairFst_pair]
  · cases right <;> simp only [CoefficientMarkedRecordFieldQuery.rightRoot, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet,
      Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair]

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  CoefficientMarkedRecordFieldVariables.polynomial mass cutoff signCutoff

/-- All derivative orders of the ACTUAL default Field query keep their signs
on ANY one actual complete row curve. The other context is a literal source
address, not an independently supplied source or characteristic polynomial. -/
theorem sign_on_root_curve (right : Bool) (z : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha right z ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFieldVariables.count hn ht ha right z) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (CoefficientMarkedRecordFieldQuery.rightRoot right z)) le_rfl u.val (x u))
    (k : ℕ) (u v : Ioo a b) :
    SignType.sign ((CoefficientMarkedRecordFieldVariables.polynomial hn ht ha right z k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((CoefficientMarkedRecordFieldVariables.polynomial hn ht ha right z k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let ctx := CoefficientMarkedRecordFieldQuery.rightRoot right z
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ i, (p i).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []) 1)
  have hpm : ∀ i j, coefficientMass ((p i).coeff j) ≤ 2^mass hn ht ha right z := by
    intro i j
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] i j).2.trans
        (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hqm : ∀ e, coefficientMass ((CoefficientMarkedRecordFieldVariables.polynomial hn ht ha right z k).coeff e) ≤
      2^mass hn ht ha right z := by
    intro e
    unfold mass
    exact (CoefficientMarkedRecordFieldVariables.coefficient_degree_mass hn ht ha right z k e).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha right z ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (sign_cutoff_le hn ht ha right z)).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha right z)
    (mass hn ht ha right z) hd (query_degree hn ht ha right z k) hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] y.val (x y) (hx y)

end LeanCanny.Encoding.CoefficientMarkedRecordFieldSign
