/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
/-! # Original parameter boxes for full clipped physical cut coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open CoefficientMarkedRecordCutCoefficientBounds (coefficientOffset coefficientBudget)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

private theorem native_mass (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (requested tau : ℕ) :
    let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
    let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
      (IntegralMixedCausalRecordPlanBits.code ctx k)
    MvMass.mass (native (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk.le) x
      (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)
      ⟨c.rule (commonDenominator x) (commonDenominator_ne_zero x),
        c.kind (commonDenominator x) (commonDenominator_ne_zero x)⟩ requested tau) ≤
      2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx + coefficientOffset hn ht ha ctx) := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let m := CoefficientMarkedRecordCutSource.birth (n := n) ctx k
  let B := CoefficientMarkedIntegerBirth.width hn ht ha ctx
  let H := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx +
    IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R m (IntegralMixedCausalRecordPlanBits.code ctx k)
  let K := IntegralMixedRelativeCuts.atChoice (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (c.kind (commonDenominator x) (commonDenominator_ne_zero x)) requested
  let f := IntegralMixedRelativeCuts.factor x (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)
    (c.rule (commonDenominator x) (commonDenominator_ne_zero x)) K
  have HM : MvMass.mass (x.sampler.scalarPrefix.basis.representative (f.coeff tau)) ≤
      FixedWidthPolynomial.count m B * 2 ^ H := by
    apply PaddedIntegralParameterExtension.representative_mass
    intro r
    have HE := CoefficientMarkedRecordFactorQueryProfile.native_kind_bound hn ht ha ctx R k hk hc K tau r.val
      (IntegralCoordinateBasis.zeroFin m B).val
    rw [IntegralCriticalTotalSnapshotBits.integerEntry_fin] at HE
    exact HE
  dsimp only [native, query, CoefficientMarkedRecordChoiceFactor.nativeFactors]
  rw [IntegralCoordinateBasis.polynomial_coefficient]
  apply ((MvMass.rename_le _ _).trans ((CoordinatePowerSubstitution.mass_le _ _).trans HM)).trans
  rw [FixedWidthPolynomial.count, ← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have HB := Nat.mul_le_mul_right B (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)
  have HB' := (Nat.mul_comm B m).le.trans HB
  dsimp only [coefficientOffset, H, m, B] at *
  omega

theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (requested tau : ℕ) (v : ℕ →₀ ℕ) :
    ((polynomial hn ht ha ctx k hk.le requested tau).coeff v).natDegree ≤
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx ∧
    coefficientMass ((polynomial hn ht ha ctx k hk.le requested tau).coeff v) ≤
      2 ^ coefficientBudget hn ht ha ctx := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := congrArg (fun p : MvPolynomial ℕ ℤ => p.coeff v)
    (specializes_native hn ht ha ctx (fun _ => r) k hk.le hr requested tau)
  rw [MvPolynomial.coeff_map] at HS
  change ((polynomial hn ht ha ctx k hk.le requested tau).coeff v).eval ((2 : ℤ)^r) = _ at HS
  rw [HS]
  exact (MvMass.coeff_le _ v).trans (native_mass hn ht ha ctx (fun _ => r) k hk hc requested tau)

end LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
