/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRowPersistence
public import LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysicalSpatial
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalBranchSign
/-! # All historical cut coefficients on ONE complete physical tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutQueries
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure CutLabel (ctx : List Bool) where
  stage : ℕ
  stage_lt : stage < IntegralMixedCausalRecordPlanBits.count ctx
  is_cut : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx stage) = false
  requested : ℕ
  coefficient : ℕ

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev count (ctx : List Bool) := CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx
abbrev Label (ctx : List Bool) := Fin (count hn ht ha ctx) ⊕ CutLabel ctx

theorem support_bound (ctx : List Bool) (q : CutLabel ctx) :
    ∀ i ∈ (CoefficientMarkedRecordChoicePhysical.polynomial hn ht ha ctx q.stage q.stage_lt.le
      q.requested q.coefficient).vars, i < count hn ht ha ctx := by
  intro i hi
  have hp := Finset.mem_range.mp (CoefficientMarkedRecordChoicePhysical.variable_box hn ht ha ctx
    q.stage q.stage_lt.le q.requested q.coefficient hi)
  exact hp.trans_le (CoefficientMarkedRecordRowPersistence.count_mono hn ht ha ctx q.stage
    (IntegralMixedCausalRecordPlanBits.count ctx) q.stage_lt.le le_rfl q.stage_lt.le)

noncomputable def coefficientQuery (ctx : List Bool) (q : CutLabel ctx) :
    MvPolynomial (Fin (count hn ht ha ctx)) ℤ[X] :=
  CoefficientFinitePhysicalQuery.polynomial (count hn ht ha ctx)
    (CoefficientMarkedRecordChoicePhysical.polynomial hn ht ha ctx q.stage q.stage_lt.le q.requested q.coefficient)
    (support_bound hn ht ha ctx q)

noncomputable def polynomial (ctx : List Bool) : Label hn ht ha ctx → MvPolynomial (Fin (count hn ht ha ctx)) ℤ[X]
  | .inl i => MvPolynomial.X i
  | .inr q => coefficientQuery hn ht ha ctx q

noncomputable def spatialDegree (ctx : List Bool) := CoefficientMarkedRecordChoicePhysical.spatialDegree hn ht ha ctx + 1

theorem count_unary : UnaryFn (count hn ht ha) := CoefficientMarkedRecordCriticalBranchSign.count_unary hn ht ha

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) :=
  (CoefficientMarkedRecordChoicePhysical.spatialDegree_binary hn ht ha).add (BinaryFn.const 1)

/-- The single full tuple contains every earlier parent physical column. -/
theorem coefficient_rename (ctx : List Bool) (q : CutLabel ctx) :
    MvPolynomial.rename Fin.val (coefficientQuery hn ht ha ctx q) =
      CoefficientMarkedRecordChoicePhysical.polynomial hn ht ha ctx q.stage q.stage_lt.le q.requested q.coefficient :=
  CoefficientFinitePhysicalQuery.rename_polynomial _ _ _

theorem polynomial_degree (ctx : List Bool) (q : Label hn ht ha ctx) :
    (polynomial hn ht ha ctx q).totalDegree ≤ spatialDegree hn ht ha ctx := by
  cases q with
  | inl i =>
    exact (MvPolynomial.totalDegree_X (R := ℤ[X]) i).le.trans (by unfold spatialDegree; omega)
  | inr q =>
    unfold polynomial coefficientQuery
    rw [CoefficientFinitePhysicalQuery.degree_eq]
    exact (CoefficientMarkedRecordChoicePhysical.spatial_degree hn ht ha ctx q.stage q.stage_lt.le
      q.requested q.coefficient).trans (Nat.le_succ _)

theorem coefficient_mass (ctx : List Bool) (q : Label hn ht ha ctx) (e : Fin (count hn ht ha ctx) →₀ ℕ) :
    coefficientMass ((polynomial hn ht ha ctx q).coeff e) ≤
      2 ^ CoefficientMarkedRecordCutCoefficientBounds.coefficientBudget hn ht ha ctx := by
  cases q with
  | inl i =>
    dsimp only [polynomial]
    rw [MvPolynomial.coeff_X]
    split_ifs
    · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
        (show 1 ≤ 2 ^ CoefficientMarkedRecordCutCoefficientBounds.coefficientBudget hn ht ha ctx from Nat.one_le_two_pow)
    · simp only [← Polynomial.C_0, coefficientMass_C, Int.natAbs_zero, Nat.zero_le]
  | inr q =>
    unfold polynomial coefficientQuery
    rw [CoefficientFinitePhysicalQuery.coefficient]
    exact (CoefficientMarkedRecordChoicePhysical.coefficient_degree_mass hn ht ha ctx q.stage
      q.stage_lt q.is_cut q.requested q.coefficient _).2

/-- Arbitrary earlier-cut requests evaluate on the SAME full tuple, with no
independently selected old root or native word. -/
theorem coefficient_evaluation (ctx : List Bool) (q : CutLabel ctx) (β : ℝ)
    (z : Fin (count hn ht ha ctx) → ℝ) :
    (coefficientQuery hn ht ha ctx q).eval₂ (SymbolicScaledSquarefree.scalarEvaluation β) z =
      (CoefficientMarkedRecordChoicePhysical.polynomial hn ht ha ctx q.stage q.stage_lt.le q.requested q.coefficient).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural z) :=
  CoefficientFinitePhysicalQuery.evaluation _ _ _ _ _

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutQueries
