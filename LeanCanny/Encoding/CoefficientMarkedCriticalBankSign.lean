/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankVariables
/-! # Original cutoffs for ALL actual critical-bank derivative queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalBankSign
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem le_succ_mul (a b : ℕ) : b ≤ (a + 1) * b := by
  calc
    b ≤ a * b + b := Nat.le_add_left _ _
    _ = (a + 1) * b := by rw [Nat.add_mul, Nat.one_mul]

theorem power_le (child : Bool) (q : List Bool) (i : ℕ) :
    CoefficientMarkedCriticalBankQuery.power hn ht ha child q i ≤
      CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) := by
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let S := P.cap (IntegralMixedPhysicalCriticalQuery.root q) + 1
  let N := 2 ^ P.width (IntegralMixedPhysicalCriticalQuery.root q)
  have hb := IntegralMixedPhysicalCriticalPrefixes.birth_le hn ht ha (BinaryFn.const 0) false child q
  change IntegralMixedPhysicalCriticalPrefixes.birth n false child q ≤ S at hb
  have hm : IntegralMixedPhysicalCriticalPrefixes.birth n false child q - 1 -
      CoefficientMarkedCriticalBankQuery.selected n child q i ≤ S :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hb)
  have hh := UniformIntegralPowerSchedule.birth_le S N _ hm
  have h1 := le_succ_mul (2 * UniformIntegralPowerSchedule.cap S N) (UniformIntegralPowerSchedule.birth S N S)
  have h2 := le_succ_mul (N + P.degree (IntegralMixedPhysicalCriticalQuery.root q))
    ((2 * UniformIntegralPowerSchedule.cap S N + 1) * UniformIntegralPowerSchedule.birth S N S)
  exact hh.trans (h1.trans h2)

noncomputable def spatialDegree (q : List Bool) :=
  (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q) *
    CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) :=
  ((BinaryFn.const 2).mul (IntegralMixedPhysicalCriticalBankEquality.catalogDegree_binary hn ht ha)).mul
    ((CoefficientMarkedRecordRowDegree.spatialDegree_binary hn ht ha).comp pairFst_mem_FP)

theorem query_degree (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    (CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).totalDegree ≤ spatialDegree hn ht ha q :=
  (CoefficientMarkedCriticalBankVariables.degree hn ht ha child q hc i k).trans
    (Nat.mul_le_mul_left _ (power_le hn ht ha child q i.val))

def packet (child : Bool) (q : List Bool) := pair (IntegralMixedPhysicalCriticalQuery.root q)
  (List.replicate (CoefficientMarkedCriticalBankQuery.stage child q) true)

theorem packet_FP (child : Bool) : packet child ∈ FP := mem_FP_pair pairFst_mem_FP
  (((IntegralMixedCausalRecordPlanBits.count_unary.comp pairFst_mem_FP).sub (UnaryFn.const (if child then 0 else 1))).mem_FP)

theorem count_unary (child : Bool) : UnaryFn (CoefficientMarkedCriticalBankVariables.count hn ht ha child) :=
  ((CoefficientMarkedRecordFullHeadControls.count_unary hn ht ha).comp (packet_FP child)).of_eq (fun q => by
    simp only [packet, CoefficientMarkedCriticalBankVariables.count, CoefficientMarkedRecordFullHeadControls.count,
      CoefficientMarkedRecordFullHeadControls.context, CoefficientMarkedRecordFullHeadControls.stage,
      pairFst_pair, pairSnd_pair, List.length_replicate, min_eq_left (Nat.sub_le _ _)])

noncomputable def mass (q : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) +
  CoefficientMarkedCriticalBankQuery.coefficientBudget hn ht ha q

theorem mass_binary : BinaryFn (mass hn ht ha) :=
  BinaryFn.add ((CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).comp pairFst_mem_FP)
    (CoefficientMarkedCriticalBankQuery.coefficientBudget_binary hn ht ha)

noncomputable def signCutoff (child : Bool) (q : List Bool) :=
  ParameterizedGridQuerySign.cutoffBudget (CoefficientMarkedCriticalBankVariables.count hn ht ha child q)
    (ParameterizedGridQuerySign.commonWidth (CoefficientMarkedCriticalBankVariables.count hn ht ha child q)
      (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
      (spatialDegree hn ht ha q)) (mass hn ht ha q)

theorem signCutoff_binary (child : Bool) : BinaryFn (signCutoff hn ht ha child) :=
  ParameterizedGridQuerySign.commonCutoff_binary (count_unary hn ht ha child)
    ((CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha).comp pairFst_mem_FP)
    (spatialDegree_binary hn ht ha) (mass_binary hn ht ha)

noncomputable def cutoff (q : List Bool) :=
  CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) +
    signCutoff hn ht ha false q + signCutoff hn ht ha true q + 1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((BinaryFn.add ((CoefficientMarkedRecordCartesianRows.cutoff_binary hn ht ha).comp pairFst_mem_FP)
    (signCutoff_binary hn ht ha false)).add (signCutoff_binary hn ht ha true)).add (BinaryFn.const 1)

theorem sign_cutoff_le (child : Bool) (q : List Bool) : signCutoff hn ht ha child q ≤ cutoff hn ht ha q := by
  unfold cutoff
  cases child <;> omega

theorem row_cutoff_le (q : List Bool) :
    CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  CoefficientMarkedCriticalBankVariables.polynomial mass cutoff signCutoff

/-- Every catalogue coordinate and derivative order is preserved on ANY
actual root curve, with all head/query bounds and cutoff constructed internally. -/
theorem sign_on_root_curve (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedCriticalBankVariables.count hn ht ha child q) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) u.val (x u))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) (u v : Ioo a b) :
    SignType.sign ((CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation u.val) (x u)) =
    SignType.sign ((CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation v.val) (x v)) := by
  let ctx := IntegralMixedPhysicalCriticalQuery.root q
  let stage := CoefficientMarkedCriticalBankQuery.stage child q
  let p := CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx stage (Nat.sub_le _ _) []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx stage (Nat.sub_le _ _) []
  have hd : ∀ j, (p j).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro j
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx stage (Nat.sub_le _ _) [] j).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx stage (Nat.sub_le _ _) []) 1)
  have hpm : ∀ j l, coefficientMass ((p j).coeff l) ≤ 2 ^ mass hn ht ha q := by
    intro j l
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx stage (Nat.sub_le _ _) [] j l).2.trans
      (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hqm : ∀ e, coefficientMass ((CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).coeff e) ≤
      2 ^ mass hn ht ha q := by
    intro e
    unfold mass
    exact (CoefficientMarkedCriticalBankVariables.coefficient_degree_mass hn ht ha child q hc i k e).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hstart : (2 : ℝ)^signCutoff hn ht ha child q ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (sign_cutoff_le hn ht ha child q)).trans ha0
  unfold signCutoff at hstart
  apply ParameterizedGridQuerySign.sign_after_common_input_bounds p _ hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha q) (mass hn ht ha q)
    hd (query_degree hn ht ha child q hc i k) hpm hqm hstart x _ u v
  intro y
  exact CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx stage (Nat.sub_le _ _) [] y.val (x y) (hx y)

/-- ONE actual complete finite root family preserves the entire bank-query
catalogue. Every head, row, query and quantitative bound is the actual one. -/
theorem exists_branches (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a) (s : Ioo a b) :
    ∃ curve : CoefficientMarkedRecordRootBranches.Curve hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) a b s,
      Finite (CoefficientMarkedRecordRootBranches.RootIndex hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) s curve) ∧
      (∀ l : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
          (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) s curve,
        ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
          (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) u.val (curve l.val u)) ∧
      (∀ u : Ioo a b, ∀ z, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
          (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) u.val z ↔
        ∃! l : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
          (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) s curve, curve l.val u = z) ∧
      (∀ l : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
          (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) s curve,
        ∀ i : Fin (CoefficientMarkedCriticalBankSource.birth n q), ∀ k, ∀ u v : Ioo a b,
        SignType.sign ((CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).eval₂
          (SymbolicScaledSquarefree.scalarEvaluation u.val) (curve l.val u)) =
        SignType.sign ((CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).eval₂
          (SymbolicScaledSquarefree.scalarEvaluation v.val) (curve l.val v))) := by
  have hrow : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (row_cutoff_le hn ht ha q)).trans ha0
  obtain ⟨curve, hf, hr, hcov⟩ := CoefficientMarkedRecordRootBranches.exists_branches hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root q) (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) hrow s
  exact ⟨curve, hf, hr, hcov, fun l i k u v => sign_on_root_curve hn ht ha child q hc ha0 (curve l.val) (hr l) i k u v⟩

end LeanCanny.Encoding.CoefficientMarkedCriticalBankSign
