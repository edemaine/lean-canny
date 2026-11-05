/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
/-! # Original coefficient and physical boxes for the actual order query -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight (coordinateSlope coordinateOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def slope (ctx : List Bool) := 2*coordinateSlope hn ht ha ctx
noncomputable def offset (ctx : List Bool) := 2*coordinateOffset hn ht ha ctx
noncomputable def productBudget (ctx : List Bool) := IntegerPolynomialDyadic.massBudget
  (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx) (slope hn ht ha ctx) (offset hn ht ha ctx)

theorem slope_binary : BinaryFn (slope hn ht ha) := (BinaryFn.const 2).mul
  (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha)
theorem offset_binary : BinaryFn (offset hn ht ha) := (BinaryFn.const 2).mul
  (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha)
theorem productBudget_binary : BinaryFn (productBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (slope_binary hn ht ha) (offset_binary hn ht ha)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed CoefficientMarkedRecordRows.symbolic

/-- Both factors are the computed common integer/cofactor of the actual
terminal bank. Their original bound is uniform over all selectors. -/
theorem product_degree_mass (ctx : List Bool) (index : ℕ) :
    (CoefficientMarkedRecordBankProducts.common hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx)*
      CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) index).natDegree ≤ slope hn ht ha ctx ∧
    coefficientMass (CoefficientMarkedRecordBankProducts.common hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx)*
      CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) index) ≤ 2^productBudget hn ht ha ctx := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HP := CoefficientMarkedRecordFullCutWindow.terminal_products hn ht ha (BinaryFn.const r) ctx index hr
  let F := IntegralMixedFramedWindowQuery.family (certifiedParameters hn ht ha (BinaryFn.const r))
    (certifiedPlan hn ht ha (BinaryFn.const r)) (certifiedData hn ht ha (BinaryFn.const r)) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha) (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha (fun _ => r))
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_affine_inputs hn ht ha (BinaryFn.const r))
    (fun _ => CoefficientMarkedRecordRawCutMetadata.terminal (n := n) ctx) (fun _ => index)
  have HD := F.scalars.denominator_bound []
  have HN := F.scalars.numerator_bound []
  have HM := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_coordinate_mass_affine hn ht ha (BinaryFn.const r)
    (CoefficientMarkedRecordRawCutMetadata.terminal (n := n) ctx)
  rw [show pairFst (CoefficientMarkedRecordRawCutMetadata.terminal (n := n) ctx) = ctx from
    CoefficientMarkedRecordRowLayout.key_root _ _ _] at HM
  rw [Polynomial.eval_mul, HP.1, HP.2, Int.natAbs_mul]
  apply (Nat.mul_le_mul HD HN).trans
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  rw [← two_mul]
  change 2*IntegralMixedFramedBankTermBits.coordinateMass (certifiedParameters hn ht ha (BinaryFn.const r))
    (certifiedPlan hn ht ha (BinaryFn.const r)) (certifiedData hn ht ha (BinaryFn.const r))
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha (fun _ => r))
    (CoefficientMarkedRecordRawCutMetadata.terminal (n := n) ctx) ≤ _
  dsimp only [slope, offset]
  nlinarith only [HM]

private theorem raw_coefficient {R : Type*} [CommRing R] (m : ℕ) (Q c : R) (i power : ℕ) (e : Fin m →₀ ℕ) :
    (raw m Q c i power).coeff e =
      if hi : i < m then if Finsupp.single ⟨i, hi⟩ power = e then Q*c else 0 else 0 := by
  by_cases hi : i < m
  · simp only [raw, dite_eq_left hi, MvPolynomial.coeff_monomial]
  · simp [raw, hi]

theorem scalarRaw_coefficient_degree_mass (ctx : List Bool) (index : ℕ)
    (e : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) →₀ ℕ) :
    ((scalarRaw hn ht ha ctx index).coeff e).natDegree ≤ slope hn ht ha ctx ∧
      coefficientMass ((scalarRaw hn ht ha ctx index).coeff e) ≤ 2^productBudget hn ht ha ctx := by
  unfold scalarRaw
  rw [raw_coefficient]
  split_ifs
  · exact product_degree_mass hn ht ha ctx index
  all_goals simp only [Polynomial.natDegree_zero, coefficientMass_zero, Nat.zero_le, and_self]

theorem scalar_coefficient_degree_mass (ctx : List Bool) (left right : ℕ)
    (e : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) →₀ ℕ) :
    ((scalar hn ht ha ctx left right).coeff e).natDegree ≤ slope hn ht ha ctx ∧
      coefficientMass ((scalar hn ht ha ctx left right).coeff e) ≤ 2^(productBudget hn ht ha ctx+1) := by
  have HL := scalarRaw_coefficient_degree_mass hn ht ha ctx left e
  have HR := scalarRaw_coefficient_degree_mass hn ht ha ctx right e
  unfold scalar
  rw [MvPolynomial.coeff_sub]
  refine ⟨(Polynomial.natDegree_sub_le _ _).trans (max_le HR.1 HL.1), ?_⟩
  apply (coefficientMass_sub_le _ _).trans ((Nat.add_le_add HR.2 HL.2).trans_eq ?_)
  rw [pow_succ]
  omega

private theorem renamed_raw_coefficient {R : Type*} [CommRing R] (m : ℕ) (Q c : R)
    (i power : ℕ) (f : Fin m → ℕ) (e : ℕ →₀ ℕ) :
    (MvPolynomial.rename f (raw m Q c i power)).coeff e =
      if hi : i < m then if Finsupp.single (f ⟨i, hi⟩) power = e then Q*c else 0 else 0 := by
  by_cases hi : i < m
  · simp only [raw, dite_eq_left hi, MvPolynomial.rename_monomial, Finsupp.mapDomain_single,
      MvPolynomial.coeff_monomial]
  · simp [raw, hi]

theorem coefficient_degree_mass (ctx : List Bool) (left right : ℕ) (e : ℕ →₀ ℕ) :
    ((polynomial hn ht ha ctx left right).coeff e).natDegree ≤ slope hn ht ha ctx ∧
      coefficientMass ((polynomial hn ht ha ctx left right).coeff e) ≤ 2^(productBudget hn ht ha ctx+1) := by
  have HB (i : ℕ) :
      ((MvPolynomial.rename (fun j => scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) j.val)
        (scalarRaw hn ht ha ctx i)).coeff e).natDegree ≤ slope hn ht ha ctx ∧
      coefficientMass ((MvPolynomial.rename (fun j => scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) j.val)
        (scalarRaw hn ht ha ctx i)).coeff e) ≤ 2^productBudget hn ht ha ctx := by
    unfold scalarRaw
    rw [renamed_raw_coefficient]
    split_ifs
    · exact product_degree_mass hn ht ha ctx i
    all_goals simp only [Polynomial.natDegree_zero, coefficientMass_zero, Nat.zero_le, and_self]
  unfold polynomial scalar
  rw [map_sub, MvPolynomial.coeff_sub]
  refine ⟨(Polynomial.natDegree_sub_le _ _).trans (max_le (HB right).1 (HB left).1), ?_⟩
  exact (coefficientMass_sub_le _ _).trans ((Nat.add_le_add (HB right).2 (HB left).2).trans_eq (by rw [pow_succ]; omega))

private theorem raw_degree {R : Type*} [CommRing R] (m : ℕ) (Q c : R) (i power : ℕ) :
    (raw m Q c i power).totalDegree ≤ power := by
  unfold raw
  split_ifs
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp

theorem weight_le (ctx : List Bool) (index : ℕ) :
    CoefficientMarkedRecordFullCutWindow.weight hn ht ha ctx index ≤ CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx := by
  apply UniformIntegralPowerSchedule.birth_le
  have HB : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ≤ CoefficientMarkedRecordActual.horizon hn ht ha ctx := by
    change IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+IntegralMixedCausalRecordPlanBits.count ctx ≤
      IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+IntegralMixedCausalRecordPlanBits.count ctx+2+1
    omega
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans HB)

theorem spatial_degree (ctx : List Bool) (left right : ℕ) :
    (polynomial hn ht ha ctx left right).totalDegree ≤ CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx := by
  unfold polynomial
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  unfold scalar
  apply (MvPolynomial.totalDegree_sub _ _).trans
  exact max_le ((raw_degree _ _ _ _ _).trans (weight_le hn ht ha ctx right))
    ((raw_degree _ _ _ _ _).trans (weight_le hn ht ha ctx left))

theorem variable_box (ctx : List Bool) (left right : ℕ) :
    ∀ i ∈ (polynomial hn ht ha ctx left right).vars,
      i < (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count := by
  intro i hi
  exact Finset.mem_range.mp (scalarApply_vars _ (CoefficientMarkedRecordFullCutPhysical.count_pos hn ht ha ctx) _ hi)

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderQuery
