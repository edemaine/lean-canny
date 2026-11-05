/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordAllCutProfile
public import LeanCanny.Algebra.PaddedIntegralEquationMass
/-! # Original parameter bounds for every actual raw-cut coefficient representative -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCutCoefficientBounds
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def coefficientOffset (ctx : List Bool) : ℕ :=
  IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx +
    CoefficientMarkedRecordActual.horizon hn ht ha ctx * CoefficientMarkedIntegerBirth.width hn ht ha ctx

noncomputable def coefficientBudget (ctx : List Bool) : ℕ :=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx) (coefficientOffset hn ht ha ctx)

theorem coefficientOffset_binary : BinaryFn (coefficientOffset hn ht ha) :=
  (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset_binary hn ht ha).add
    ((BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))).mul
      (BinaryFn.ofUnary (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width))

theorem coefficientBudget_binary : BinaryFn (coefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope_binary hn ht ha) (coefficientOffset_binary hn ht ha)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordCutSource.polynomial CoefficientMarkedRecordCutSource.raw
  CoefficientMarkedRecordCutSource.nativeRaw

private theorem native_mass (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) (tau : ℕ) :
    MvMass.mass (((CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le).sampler.scalarPrefix.basis.polynomial
      (CoefficientMarkedRecordCutSource.nativeRaw hn ht ha ctx R k hk.le)).coeff tau) ≤
      2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx + coefficientOffset hn ht ha ctx) := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let m := CoefficientMarkedRecordCutSource.birth (n := n) ctx k
  let B := CoefficientMarkedIntegerBirth.width hn ht ha ctx
  let H := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx +
    IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx
  rw [IntegralCoordinateBasis.polynomial_coefficient]
  have HM : MvMass.mass (x.sampler.scalarPrefix.basis.representative
      ((CoefficientMarkedRecordCutSource.nativeRaw hn ht ha ctx R k hk.le).coeff tau)) ≤
      FixedWidthPolynomial.count m B * 2 ^ H := by
    apply PaddedIntegralParameterExtension.representative_mass
    intro r
    have HE := CoefficientMarkedRecordAllCutProfile.raw_coefficient_bound hn ht ha ctx R k hk hc tau r.val
      (IntegralCoordinateBasis.zeroFin m B).val
    dsimp only at HE
    rw [IntegralCriticalTotalSnapshotBits.integerEntry_fin] at HE
    exact HE
  apply HM.trans
  rw [FixedWidthPolynomial.count, ← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have HB := Nat.mul_le_mul_right B (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)
  have HB' := (Nat.mul_comm B m).le.trans HB
  dsimp only [coefficientOffset, H, m, B] at *
  omega

/-- Every raw target coefficient and every scalar monomial has an original bound. -/
theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (tau : ℕ) (e : Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) →₀ ℕ) :
    (((CoefficientMarkedRecordCutSource.polynomial hn ht ha ctx k).coeff tau).coeff e).natDegree ≤
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx ∧
      coefficientMass (((CoefficientMarkedRecordCutSource.polynomial hn ht ha ctx k).coeff tau).coeff e) ≤
        2 ^ coefficientBudget hn ht ha ctx := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := CoefficientMarkedRecordCutSource.specializes hn ht ha ctx (fun _ => r) k hk.le hr
  have HE := congrArg (fun p : Polynomial (MvPolynomial (Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ℤ) =>
    (p.coeff tau).coeff e) HS
  rw [Polynomial.coeff_map, MvPolynomial.coeff_map] at HE
  change (((CoefficientMarkedRecordCutSource.polynomial hn ht ha ctx k).coeff tau).coeff e).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE]
  exact (MvMass.coeff_le _ e).trans (native_mass hn ht ha ctx (fun _ => r) k hk hc tau)

noncomputable def scalarDegree (ctx : List Bool) : ℕ :=
  CoefficientMarkedRecordActual.horizon hn ht ha ctx * (2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx - 1)

theorem scalarDegree_binary : BinaryFn (scalarDegree hn ht ha) :=
  (BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))).mul
    (((BinaryFn.const 2).powUnary (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width).sub (BinaryFn.const 1))

theorem scalar_degree (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (tau : ℕ) :
    ((CoefficientMarkedRecordCutSource.polynomial hn ht ha ctx k).coeff tau).totalDegree ≤ scalarDegree hn ht ha ctx := by
  unfold CoefficientMarkedRecordCutSource.polynomial
  exact ((CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).basis.polynomial_coefficient_degree _ tau).trans
    (Nat.mul_le_mul_right _ (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk))

private theorem raw_degree (ctx : List Bool) (k : ℕ) :
    (CoefficientMarkedRecordCutSource.raw hn ht ha ctx k).natDegree ≤
      (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree := by
  unfold CoefficientMarkedRecordCutSource.raw CoefficientMixedCutSpecialization.raw CoefficientMixedCutDispatcher.raw
  exact IntegralRelativeTruncation.natDegree_le _ _

theorem target_degree (ctx : List Bool) (k : ℕ) :
    (CoefficientMarkedRecordCutSource.polynomial hn ht ha ctx k).natDegree ≤
      2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx := by
  unfold CoefficientMarkedRecordCutSource.polynomial
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro tau htau
  rw [CoefficientCoordinateBasis.polynomial_coefficient]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((raw_degree hn ht ha ctx k).trans_lt
    ((CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree_cap.trans_lt htau))]
  exact CoefficientCoordinateBasis.representative_zero _

end LeanCanny.Encoding.CoefficientMarkedRecordCutCoefficientBounds
