/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutSpatial
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Uniform original boxes for all native full-cut interval principals -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutBounds
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def slope (ctx : List Bool) := ∑ i ∈ Finset.range (IntegralMixedCausalRecordPlanBits.count ctx),
  CoefficientMarkedRecordFullCutPrincipalHeight.slope hn ht ha ctx i
noncomputable def offset (ctx : List Bool) := ∑ i ∈ Finset.range (IntegralMixedCausalRecordPlanBits.count ctx),
  CoefficientMarkedRecordFullCutPrincipalHeight.offset hn ht ha ctx i
noncomputable def spatialDegree (ctx : List Bool) := ∑ i ∈ Finset.range (IntegralMixedCausalRecordPlanBits.count ctx),
  CoefficientMarkedRecordFullCutSpatial.spatialDegree hn ht ha ctx i
noncomputable def coefficientBudget (ctx : List Bool) := IntegerPolynomialDyadic.massBudget
  (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx) (slope hn ht ha ctx) (offset hn ht ha ctx)

attribute [local irreducible] CoefficientMarkedRecordFullCutPrincipalHeight.slope
  CoefficientMarkedRecordFullCutPrincipalHeight.offset CoefficientMarkedRecordFullCutSpatial.spatialDegree

theorem slope_binary : BinaryFn (slope hn ht ha) := by
  have HF : BinaryFn (fun q => CoefficientMarkedRecordFullCutPrincipalHeight.slope hn ht ha (pairFst q) (pairSnd q).length) :=
    CoefficientMarkedRecordFullCutPrincipalHeight.slope_binary hn ht ha pairFst_mem_FP (BinaryFn.ofUnary UnaryFn.index)
  exact (BinaryFn.sum IntegralMixedCausalRecordPlanBits.count_unary HF).of_eq (fun q => by
    simp only [slope, pairFst_pair, pairSnd_pair, List.length_replicate])
theorem offset_binary : BinaryFn (offset hn ht ha) := by
  have HF : BinaryFn (fun q => CoefficientMarkedRecordFullCutPrincipalHeight.offset hn ht ha (pairFst q) (pairSnd q).length) :=
    CoefficientMarkedRecordFullCutPrincipalHeight.offset_binary hn ht ha pairFst_mem_FP (BinaryFn.ofUnary UnaryFn.index)
  exact (BinaryFn.sum IntegralMixedCausalRecordPlanBits.count_unary HF).of_eq (fun q => by
    simp only [offset, pairFst_pair, pairSnd_pair, List.length_replicate])
theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) := by
  have HF : BinaryFn (fun q => CoefficientMarkedRecordFullCutSpatial.spatialDegree hn ht ha (pairFst q) (pairSnd q).length) :=
    CoefficientMarkedRecordFullCutSpatial.spatialDegree_binary hn ht ha pairFst_mem_FP (BinaryFn.ofUnary UnaryFn.index)
  exact (BinaryFn.sum IntegralMixedCausalRecordPlanBits.count_unary HF).of_eq (fun q => by
    simp only [spatialDegree, pairFst_pair, pairSnd_pair, List.length_replicate])
theorem coefficientBudget_binary : BinaryFn (coefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (slope_binary hn ht ha) (offset_binary hn ht ha)

theorem stage_slope_le (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    CoefficientMarkedRecordFullCutPrincipalHeight.slope hn ht ha ctx k ≤ slope hn ht ha ctx :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)
theorem stage_offset_le (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    CoefficientMarkedRecordFullCutPrincipalHeight.offset hn ht ha ctx k ≤ offset hn ht ha ctx :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)
theorem stage_spatial_le (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    CoefficientMarkedRecordFullCutSpatial.spatialDegree hn ht ha ctx k ≤ spatialDegree hn ht ha ctx :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)

/-- The common original box covers every raw cut, every endpoint index,
every principal, both infinitesimal coefficients and either epsilon sign. -/
theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ) (e : ℕ →₀ ℕ) :
    ((CoefficientMarkedRecordFullCutPhysical.polynomial hn ht ha ctx k hk index 1 negative j delta epsilon).coeff e).natDegree ≤
      slope hn ht ha ctx ∧
    coefficientMass ((CoefficientMarkedRecordFullCutPhysical.polynomial hn ht ha ctx k hk index 1 negative j delta epsilon).coeff e) ≤
      2^coefficientBudget hn ht ha ctx := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := congrArg (fun p : MvPolynomial ℕ ℤ => p.coeff e)
    (CoefficientMarkedRecordFullCutPhysical.specializes hn ht ha (BinaryFn.const r) ctx k hk hc index 1 negative hr j delta epsilon)
  rw [MvPolynomial.coeff_map] at HS
  change ((CoefficientMarkedRecordFullCutPhysical.polynomial hn ht ha ctx k hk index 1 negative j delta epsilon).coeff e).eval ((2 : ℤ)^r) = _ at HS
  rw [HS]
  have HM := CoefficientMarkedRecordFullCutPhysical.native_mass hn ht ha (BinaryFn.const r) ctx k index negative j delta epsilon
  apply (MvMass.coeff_le _ e).trans ((MvMass.rename_le _ _).trans (HM.trans ?_))
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.add_le_add (Nat.mul_le_mul_right r (stage_slope_le hn ht ha ctx k hk))
    (stage_offset_le hn ht ha ctx k hk)

theorem physical_degree (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ) :
    (CoefficientMarkedRecordFullCutPhysical.polynomial hn ht ha ctx k hk index 1 negative j delta epsilon).totalDegree ≤
      spatialDegree hn ht ha ctx :=
  (CoefficientMarkedRecordFullCutSpatial.physical_degree hn ht ha ctx k hk index negative j delta epsilon).trans
    (stage_spatial_le hn ht ha ctx k hk)

noncomputable def finite (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ) :=
  CoefficientFinitePhysicalQuery.polynomial (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count
    (CoefficientMarkedRecordFullCutPhysical.polynomial hn ht ha ctx k hk index 1 negative j delta epsilon)
    (fun _i hi => Finset.mem_range.mp (CoefficientMarkedRecordFullCutPhysical.variable_box hn ht ha ctx k hk index 1 negative j delta epsilon hi))

theorem finite_degree (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ) :
    (finite hn ht ha ctx k hk index negative j delta epsilon).totalDegree ≤ spatialDegree hn ht ha ctx := by
  unfold finite
  rw [CoefficientFinitePhysicalQuery.degree_eq]
  exact physical_degree hn ht ha ctx k hk index negative j delta epsilon

theorem finite_coefficient_degree_mass (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ)
    (e : Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count →₀ ℕ) :
    ((finite hn ht ha ctx k hk index negative j delta epsilon).coeff e).natDegree ≤ slope hn ht ha ctx ∧
    coefficientMass ((finite hn ht ha ctx k hk index negative j delta epsilon).coeff e) ≤ 2^coefficientBudget hn ht ha ctx := by
  unfold finite
  rw [CoefficientFinitePhysicalQuery.coefficient]
  exact coefficient_degree_mass hn ht ha ctx k hk hc index negative j delta epsilon _

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutBounds
