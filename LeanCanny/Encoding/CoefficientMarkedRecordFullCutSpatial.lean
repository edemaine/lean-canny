/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutPhysical
public import LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysicalSpatial
/-! # Original spatial boxes for actual full-cut comparison queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutSpatial
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem monomial_degree {R : Type*} [CommRing R] {m : ℕ} (a : R) (index w : ℕ) :
    (CoefficientTarskiParameterQueries.monomial (m := m) index w a).totalDegree ≤ w := by
  unfold CoefficientTarskiParameterQueries.monomial
  split_ifs
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp only [MvPolynomial.totalDegree_zero, Nat.zero_le]

private theorem window_degree {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (q a : R) (index w : ℕ) (negative : Bool) (i : ℕ) :
    ((window (m := m) q a index w negative).coeff i).totalDegree ≤ w+1 := by
  have HE : (MvPolynomial.C (q^2)*MvPolynomial.X (0 : Fin (m+1))).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  have HM := (MvPolynomial.totalDegree_rename_le Fin.succ (monomial (m := m) index w (q*a))).trans
    (monomial_degree (q*a) index w)
  cases i with
  | zero =>
    simp only [window, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_C_zero, zero_add]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le _ (HM.trans (by omega))
    cases negative
    · exact HE.trans (by omega)
    · simpa only [Bool.false_eq_true, ite_true, MvPolynomial.totalDegree_neg] using HE.trans (by omega : 1 ≤ w+1)
  | succ i =>
    cases i <;> simp only [window, Polynomial.coeff_add, Polynomial.coeff_mul_X,
      Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, zero_add, add_zero,
      MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_zero, Nat.zero_le]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def powerBound (ctx : List Bool) := CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx
noncomputable def headBound (ctx : List Bool) := CoefficientMarkedRecordChoicePhysical.spatialDegree hn ht ha ctx
noncomputable def spatialDegree (ctx : List Bool) (k : ℕ) :=
  let d := CoefficientMarkedRecordFullCutPrincipalHeight.degree hn ht ha ctx k
  MultivariateTarskiDegreeBounds.principalDegreeBound d (d-1) (d+2) (headBound hn ht ha ctx) (powerBound hn ht ha ctx+1)

theorem head_coefficient_degree (ctx : List Bool) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) (i : ℕ) :
    ((CoefficientMarkedRecordFullCutPrincipal.head hn ht ha ctx k hk).coeff i).totalDegree ≤ headBound hn ht ha ctx := by
  unfold CoefficientMarkedRecordFullCutPrincipal.head pairLift
  rw [Polynomial.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  unfold CoefficientMarkedRecordFullCutTerminalHead.polynomial CoefficientFullCutHeadQueries.terminalHead
  rw [Polynomial.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  rw [CoefficientFullCutHeadQueries.scalarHead_coefficient]
  split_ifs
  · apply (CoordinatePowerSubstitution.degree_le _ _ (powerBound hn ht ha ctx) ?_).trans
      (Nat.mul_le_mul_left _ (CoefficientMarkedRecordChoiceFactor.scalar_degree hn ht ha ctx k hk.le
        (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx) i))
    intro j
    exact (UniformIntegralPowerSchedule.weights_le _ _ _ j).trans
      (UniformIntegralPowerSchedule.birth_le _ _ _ ((Nat.sub_le _ _).trans
        (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)))
  · simp only [MvPolynomial.totalDegree_zero, Nat.zero_le]

theorem window_weight_le (ctx : List Bool) (index : ℕ) :
    CoefficientMarkedRecordFullCutWindow.weight hn ht ha ctx index ≤ powerBound hn ht ha ctx := by
  apply UniformIntegralPowerSchedule.birth_le
  have HF : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ≤ CoefficientMarkedRecordActual.horizon hn ht ha ctx := by
    change IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+IntegralMixedCausalRecordPlanBits.count ctx ≤
      IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+IntegralMixedCausalRecordPlanBits.count ctx+2+1
    omega
  exact ((Nat.sub_le _ _).trans (Nat.sub_le _ _)).trans HF

theorem query_coefficient_degree (ctx : List Bool) (index : ℕ) (negative : Bool) (i : ℕ) :
    ((CoefficientMarkedRecordFullCutPrincipal.query hn ht ha ctx index 1 negative).coeff i).totalDegree ≤ powerBound hn ht ha ctx+1 := by
  unfold CoefficientMarkedRecordFullCutPrincipal.query
  change (((pairLift false (CoefficientMarkedRecordFullCutWindow.polynomial hn ht ha ctx index negative))^1).coeff i).totalDegree ≤ _
  rw [pow_one, pairLift, Polynomial.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans ((window_degree _ _ _ _ _ _).trans
    (Nat.add_le_add_right (window_weight_le hn ht ha ctx index) 1))

theorem principal_degree (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (negative : Bool) (j : ℕ) :
    (CoefficientMarkedRecordFullCutPrincipal.polynomial hn ht ha ctx k hk index 1 negative j).totalDegree ≤
      spatialDegree hn ht ha ctx k :=
  MultivariateTarskiDegreeBounds.principal_seed _ _ _ _ _ _ _ _
    (head_coefficient_degree hn ht ha ctx k hk) (query_coefficient_degree hn ht ha ctx index negative)

theorem physical_degree (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ) :
    (CoefficientMarkedRecordFullCutPhysical.polynomial hn ht ha ctx k hk index 1 negative j delta epsilon).totalDegree ≤
      spatialDegree hn ht ha ctx k :=
  (MvPolynomial.totalDegree_rename_le _ _).trans ((MvTwoParameterCoefficient.degree _ _ _).trans
    ((MvPolynomial.totalDegree_rename_le _ _).trans (principal_degree hn ht ha ctx k hk index negative j)))

theorem spatialDegree_binary {ctx : List Bool → List Bool} {k : List Bool → ℕ}
    (hctx : ctx ∈ FP) (hk : BinaryFn k) : BinaryFn (fun q => spatialDegree hn ht ha (ctx q) (k q)) := by
  have HW : BinaryFn (fun q => powerBound hn ht ha (ctx q)) :=
    (CoefficientMarkedRecordTermQuery.spatialPowerBound_binary hn ht ha).comp hctx
  exact MultivariateTarskiDegreeBounds.principalDegreeBound_binary
    (CoefficientMarkedRecordFullCutPrincipalHeight.degree_binary hn ht ha hctx hk)
    ((CoefficientMarkedRecordFullCutPrincipalHeight.degree_binary hn ht ha hctx hk).sub (BinaryFn.const 1))
    ((CoefficientMarkedRecordFullCutPrincipalHeight.degree_binary hn ht ha hctx hk).add (BinaryFn.const 2))
    ((CoefficientMarkedRecordChoicePhysical.spatialDegree_binary hn ht ha).comp hctx)
    (HW.add (BinaryFn.const 1))

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutSpatial
