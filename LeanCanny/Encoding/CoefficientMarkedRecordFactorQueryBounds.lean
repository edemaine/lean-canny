/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFactorQueryProfile
public import LeanCanny.Encoding.CoefficientMarkedRecordCutCoefficientBounds
/-! # Parameter boxes for full alternative-factor guard queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFactorQueryBounds
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open CoefficientMarkedRecordCutCoefficientBounds (coefficientOffset coefficientBudget)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordFactorQuery.polynomial CoefficientMarkedRecordFactorQuery.factor CoefficientMarkedRecordFactorQuery.native

private theorem native_mass (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) (choice tau : ℕ) :
    MvMass.mass (((CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le).sampler.scalarPrefix.basis.polynomial
      (CoefficientMarkedRecordFactorQuery.native hn ht ha ctx R k hk.le choice)).coeff tau) ≤
      2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx + coefficientOffset hn ht ha ctx) := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let m := CoefficientMarkedRecordCutSource.birth (n := n) ctx k
  let B := CoefficientMarkedIntegerBirth.width hn ht ha ctx
  let H := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx +
    IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx
  rw [IntegralCoordinateBasis.polynomial_coefficient]
  have HM : MvMass.mass (x.sampler.scalarPrefix.basis.representative
      ((CoefficientMarkedRecordFactorQuery.native hn ht ha ctx R k hk.le choice).coeff tau)) ≤
      FixedWidthPolynomial.count m B * 2 ^ H := by
    apply PaddedIntegralParameterExtension.representative_mass
    intro r
    have HE := CoefficientMarkedRecordFactorQueryProfile.coefficient_bound hn ht ha ctx R k hk hc choice tau r.val
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
    (choice tau : ℕ) (e : Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) →₀ ℕ) :
    (((CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).coeff tau).coeff e).natDegree ≤
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx ∧
      coefficientMass (((CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).coeff tau).coeff e) ≤
        2 ^ coefficientBudget hn ht ha ctx := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := CoefficientMarkedRecordFactorQuery.specializes hn ht ha ctx (fun _ => r) k hk.le hr choice
  have HE := congrArg (fun p : Polynomial (MvPolynomial (Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ℤ) =>
    (p.coeff tau).coeff e) HS
  rw [Polynomial.coeff_map, MvPolynomial.coeff_map] at HE
  change (((CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).coeff tau).coeff e).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE]
  exact (MvMass.coeff_le _ e).trans (native_mass hn ht ha ctx (fun _ => r) k hk hc choice tau)

/-- Scalar representatives use the same original spatial box for every choice. -/
theorem scalar_degree (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (choice tau : ℕ) :
    ((CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).coeff tau).totalDegree ≤
      CoefficientMarkedRecordCutCoefficientBounds.scalarDegree hn ht ha ctx := by
  unfold CoefficientMarkedRecordFactorQuery.polynomial
  exact ((CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).basis.polynomial_coefficient_degree _ tau).trans
    (Nat.mul_le_mul_right _ (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk))

private theorem integral_polynomial_degree {A : Type} [CommRing A] {m N : ℕ}
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) :
    (b.polynomial p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro tau htau
  rw [IntegralCoordinateBasis.polynomial_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt htau]
  exact b.representative_zero

private theorem zero_of_dyadic_tail (p : ℤ[X]) (C : ℕ)
    (hp : ∀ r, C ≤ r → p.eval ((2 : ℤ) ^ r) = 0) : p = 0 := by
  have HD : p.natDegree ≤ 0 :=
    (IntegerPolynomialDyadic.degree_mass_of_growth p C 0 0 (by
      intro r hr
      rw [hp r hr]
      exact Nat.zero_le _)).1
  have HE := Polynomial.eq_C_of_natDegree_le_zero HD
  have HV := hp C le_rfl
  rw [HE, Polynomial.eval_C] at HV
  rw [HE, HV, Polynomial.C_0]

private theorem native_degree (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (choice : ℕ) :
    (((CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk).sampler.scalarPrefix.basis.polynomial
      (CoefficientMarkedRecordFactorQuery.native hn ht ha ctx R k hk choice))).natDegree ≤
        2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx := by
  apply (integral_polynomial_degree _ _).trans
  unfold CoefficientMarkedRecordFactorQuery.native
  exact (IntegralMixedCutNilpotent.factor_degree_lt _ _ _ _).le.trans
    (CoefficientMarkedRecordNative.source_cap hn ht ha ctx R)

/-- This bounds the FULL factor, without truncating at its stored birth degree. -/
theorem target_degree (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (choice : ℕ) :
    (CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).natDegree ≤
      2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro tau htau
  apply MvPolynomial.ext
  intro e
  change (((CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).coeff tau).coeff e) = 0
  apply zero_of_dyadic_tail _ (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
  intro r hr
  have HS := CoefficientMarkedRecordFactorQuery.specializes hn ht ha ctx (fun _ => r) k hk hr choice
  have HE := congrArg (fun p : Polynomial (MvPolynomial (Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ℤ) =>
    (p.coeff tau).coeff e) HS
  rw [Polynomial.coeff_map, MvPolynomial.coeff_map] at HE
  change (((CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k choice).coeff tau).coeff e).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE, Polynomial.coeff_eq_zero_of_natDegree_lt
    ((native_degree hn ht ha ctx (fun _ => r) k hk choice).trans_lt htau), AddMonoidAlgebra.coeff_zero]
  rfl

end LeanCanny.Encoding.CoefficientMarkedRecordFactorQueryBounds
