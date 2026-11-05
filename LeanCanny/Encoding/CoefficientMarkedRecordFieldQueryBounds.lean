/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
/-! # Original bounds for the constructed common-radius field-query family -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedPhysicalFieldEquality (catalogDegree catalogPower contextProbe)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (right : Bool) (z : List Bool) :=
  max (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldSource.root z))
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z))

noncomputable def slope (right : Bool) (z : List Bool) :=
  IntegralMixedPhysicalFieldEquality.fieldSlope hn ht ha (CoefficientMarkedRecordFieldSource.root z) +
    IntegralMixedPhysicalFieldEquality.queryRightSlope hn ht ha
      (pair (CoefficientMarkedRecordFieldSource.root z) (rightRoot right z))

noncomputable def offset (right : Bool) (z : List Bool) :=
  IntegralMixedPhysicalFieldEquality.queryOffset hn ht ha
    (pair (CoefficientMarkedRecordFieldSource.root z) (rightRoot right z))

noncomputable def coefficientBudget (right : Bool) (z : List Bool) :=
  IntegerPolynomialDyadic.massBudget (cutoff hn ht ha right z) (slope hn ht ha right z) (offset hn ht ha right z)

theorem rightRoot_FP (right : Bool) : rightRoot right ∈ FP :=
  mem_FP_comp (IntegralMixedPhysicalFieldEquality.context_FP right) pairFst_mem_FP

theorem cutoff_binary (right : Bool) : BinaryFn (cutoff hn ht ha right) := by
  have HL : BinaryFn (fun z => CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (CoefficientMarkedRecordFieldSource.root z)) :=
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp CoefficientMarkedRecordFieldSource.root_FP
  have HR : BinaryFn (fun z => CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z)) :=
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp (rightRoot_FP right)
  exact (BinaryFn.ite (HL.le HR) HR HL).of_eq (fun _ => Nat.max_def.symm)

theorem slope_binary (right : Bool) : BinaryFn (slope hn ht ha right) := by
  have HL : BinaryFn (fun z => IntegralMixedPhysicalFieldEquality.fieldSlope hn ht ha
      (CoefficientMarkedRecordFieldSource.root z)) :=
    (IntegralMixedPhysicalFieldEquality.fieldSlope_binary hn ht ha).comp CoefficientMarkedRecordFieldSource.root_FP
  have HR : BinaryFn (fun z => IntegralMixedPhysicalFieldEquality.queryRightSlope hn ht ha
      (pair (CoefficientMarkedRecordFieldSource.root z) (rightRoot right z))) :=
    (IntegralMixedPhysicalFieldEquality.queryRightSlope_binary hn ht ha).comp
      (mem_FP_pair CoefficientMarkedRecordFieldSource.root_FP (rightRoot_FP right))
  exact HL.add HR

theorem offset_binary (right : Bool) : BinaryFn (offset hn ht ha right) :=
  (IntegralMixedPhysicalFieldEquality.queryOffset_binary hn ht ha).comp
    (mem_FP_pair CoefficientMarkedRecordFieldSource.root_FP (rightRoot_FP right))

theorem coefficientBudget_binary (right : Bool) : BinaryFn (coefficientBudget hn ht ha right) :=
  IntegerPolynomialDyadic.massBudget_binary (cutoff_binary hn ht ha right) (slope_binary hn ht ha right)
    (offset_binary hn ht ha right)

theorem coefficient_degree_mass (right : Bool) (z : List Bool) (k j : ℕ) :
    ((polynomial hn ht ha right z k).coeff j).natDegree ≤ slope hn ht ha right z ∧
      coefficientMass ((polynomial hn ht ha right z k).coeff j) ≤ 2 ^ coefficientBudget hn ht ha right z := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (CoefficientMarkedRecordFieldSource.root z) ≤ r := (le_max_left _ _).trans hr
  have HR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (rightRoot right z) ≤ r := (le_max_right _ _).trans hr
  have HS := specializes hn ht ha r right z k HL HR
  have HC := congrArg (fun p : ℤ[X] => p.coeff j) HS
  rw [Polynomial.coeff_map] at HC
  change ((polynomial hn ht ha right z k).coeff j).eval ((2 : ℤ)^r) = _ at HC
  rw [HC]
  have HM := (coeff_natAbs_le_coefficientMass _ j).trans
    (IntegralMixedPhysicalFieldEquality.query_mass hn ht ha (BinaryFn.const r) right z k)
  simpa only [slope, offset, CoefficientMarkedRecordFieldSource.root, rightRoot, Nat.add_mul] using HM

theorem creating_power_binary (right : Bool) : BinaryFn (catalogPower hn ht ha right) := by
  have HC : UnaryFn (fun z => IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (rightRoot right z)) :=
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount_unary hn).comp (rightRoot_FP right)
  have HS : UnaryFn (IntegralMixedPhysicalFieldEquality.catalogSelected n right) :=
    (HC.sub (UnaryFn.const 1)).sub
      (UnaryFn.fromBitsLE_min (IntegralMixedPhysicalFieldEquality.labelWord_FP right) (HC.sub (UnaryFn.const 1)))
  exact UniformIntegralPowerSchedule.birth_binary
    (((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.comp (rightRoot_FP right)).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.comp (rightRoot_FP right)))
    ((HC.sub (UnaryFn.const 1)).sub HS)

theorem target_degree_binary (right : Bool) : BinaryFn (fun z =>
    2 * catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z) * catalogPower hn ht ha right z) :=
  ((BinaryFn.const 2).mul ((IntegralMixedPhysicalFieldEquality.catalogDegree_binary hn ht ha).comp
    CoefficientMarkedRecordFieldSource.root_FP)).mul (creating_power_binary hn ht ha right)

theorem target_degree (right : Bool) (z : List Bool) (k : ℕ) :
    (polynomial hn ht ha right z k).natDegree ≤
      2 * catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z) * catalogPower hn ht ha right z := by
  unfold polynomial CoefficientBankUnivariateQuery.polynomial
  rw [Polynomial.natDegree_expand]
  apply Nat.mul_le_mul_right
  have HD := UnivariateRational.clear_degree
    (2 * catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z))
    (Polynomial.derivative^[k] (CoefficientMarkedRecordFieldSource.polynomial hn ht ha z))
    (C (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) (IntegralMixedPhysicalFieldEquality.catalogSelected n right z)) * X)
    (C (CoefficientMarkedRecordBankProducts.common hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)))) 1
    (by simpa only [Polynomial.natDegree_X] using Polynomial.natDegree_C_mul_le _ (X : Polynomial ℤ[X]))
    (by rw [Polynomial.natDegree_C]; omega)
  simpa only [Nat.mul_one] using HD

end LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
