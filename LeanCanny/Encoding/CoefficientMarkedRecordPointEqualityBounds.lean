/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalBranchSign
/-! # Original bounds for the actual two-powered-column equality query -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def spatialDegree (ctx : List Bool) :=
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  UniformIntegralPowerSchedule.physical (P.cap ctx+1) (2^P.width ctx) (P.cap ctx+2)

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) := by
  let A := IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha
  exact UniformIntegralPowerSchedule.physical_binary (A.cap.add (UnaryFn.const 1))
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp A.width) (A.cap.add (UnaryFn.const 2))

theorem query_degree (ctx : List Bool) (a b i : ℕ)
    (ha0 : a ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    (hb0 : b ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1) :
    (polynomial hn ht ha ctx a b i).totalDegree ≤ spatialDegree hn ht ha ctx := by
  apply (PolynomialMapDegree.degree_le _ _).trans
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  apply (IntegralMixedFramedPointEqualityBits.polynomial_degree _ _ _ _ _ _ []).trans
  apply max_le
  all_goals
    unfold IntegralMixedFramedCriticalGuardBits.physicalPower spatialDegree
    simp only [key, CoefficientMarkedRecordRowLayout.key_root]
    exact (UniformIntegralPowerSchedule.physical_le _ _ _ (by omega)).trans_eq (by rfl)

theorem integer_mass (ctx : List Bool) (a b i : ℕ) :
    MvMass.mass (integer hn ht ha ctx a b i) ≤ 2^1 :=
  (MvMass.rename_le _ _).trans (IntegralMixedFramedPointEqualityBits.polynomial_mass _ _ _ _ _ _ [])

theorem coefficient_mass (ctx : List Bool) (a b i : ℕ) (e) :
    coefficientMass ((polynomial hn ht ha ctx a b i).coeff e) ≤ 2^1 := by
  simp only [polynomial, MvPolynomial.coeff_map, coefficientMass_C]
  exact (MvMass.coeff_le _ _).trans (integer_mass hn ht ha ctx a b i)

private theorem eval_constant {m : ℕ} (p : MvPolynomial (Fin m) ℤ) (r : ℝ) (z : Fin m → ℝ) :
    (MvPolynomial.map (Polynomial.C : ℤ →+* ℤ[X]) p).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation r) z = p.eval₂ (Int.castRingHom ℝ) z := by
  rw [MvPolynomial.eval₂_map]
  congr 1
  exact Subsingleton.elim _ _

noncomputable def mass (ctx : List Bool) := CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx+1
theorem mass_binary : BinaryFn (mass hn ht ha) :=
  (CoefficientMarkedRecordCartesianRows.mass_binary hn ht ha).add (BinaryFn.const 1)

noncomputable def cutoff (ctx : List Bool) := ParameterizedGridQuerySign.cutoffBudget
  (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count
  (ParameterizedGridQuerySign.commonWidth
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha ctx)) (mass hn ht ha ctx)

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ParameterizedGridQuerySign.commonCutoff_binary (CoefficientMarkedRecordCriticalBranchSign.count_unary hn ht ha)
    (CoefficientMarkedRecordCartesianRows.headDegree_binary hn ht ha) (spatialDegree_binary hn ht ha) (mass_binary hn ht ha)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordFullHeads.polynomial
  polynomial mass cutoff

theorem sign_on_root_curve (ctx : List Bool) (s t i : ℕ)
    (hs : s ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    (ht0 : t ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u)) (u v : Ioo a b) :
    SignType.sign ((integer hn ht ha ctx s t i).eval₂ (Int.castRingHom ℝ) (x u)) =
    SignType.sign ((integer hn ht ha ctx s t i).eval₂ (Int.castRingHom ℝ) (x v)) := by
  let p : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → Polynomial (Polynomial ℤ) :=
    CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  have hd : ∀ j, (p j).natDegree ≤ CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro j
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] j).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx
        (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []) 1)
  have hpm : ∀ j k, coefficientMass ((p j).coeff k) ≤ 2^mass hn ht ha ctx := by
    intro j k
    unfold mass CoefficientMarkedRecordCartesianRows.mass
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] j k).2.trans
        (Nat.pow_le_pow_right (by decide) (by omega))
  have hqm : ∀ e, coefficientMass ((polynomial hn ht ha ctx s t i).coeff e) ≤ 2^mass hn ht ha ctx :=
    fun e => (coefficient_mass hn ht ha ctx s t i e).trans (Nat.pow_le_pow_right (by decide) (by unfold mass; omega))
  unfold cutoff at ha0
  have H := ParameterizedGridQuerySign.sign_after_common_input_bounds p (polynomial hn ht ha ctx s t i) hp
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx) (spatialDegree hn ht ha ctx) (mass hn ht ha ctx)
    hd (query_degree hn ht ha ctx s t i hs ht0) hpm hqm ha0 x
    (fun y => CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] y.val (x y) (hx y)) u v
  unfold polynomial at H
  rw [eval_constant, eval_constant] at H
  exact H

end LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
