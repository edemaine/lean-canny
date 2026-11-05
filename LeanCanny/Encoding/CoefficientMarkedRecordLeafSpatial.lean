/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
public import LeanCanny.Algebra.UnivariateInfinity
/-! # Original spatial bounds for every literal marked integer leaf -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem physical_degree {R : Type*} [CommRing R] {ι : Type*}
    (p : Polynomial R) (D w : ℕ) (a b : R) (column : ι) :
    (CoefficientBankUnivariateQuery.physical p D w a b column).totalDegree ≤ D*w := by
  unfold CoefficientBankUnivariateQuery.physical
  apply (UnivariateInfinity.degree_le _ _).trans
  unfold CoefficientBankUnivariateQuery.polynomial
  rw [Polynomial.natDegree_expand]
  apply Nat.mul_le_mul_right
  have h := UnivariateRational.clear_degree D p (C a*X) (C b) 1
    ((Polynomial.natDegree_C_mul_le a (X : Polynomial R)).trans Polynomial.natDegree_X_le)
    (by rw [Polynomial.natDegree_C]; omega)
  simpa only [Nat.mul_one] using h

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def spatialDegree (ctx : List Bool) :=
  2*degreeCap hn ht ha ctx*CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) :=
  ((BinaryFn.const 2).mul (degreeCap_binary hn ht ha)).mul
    (CoefficientMarkedRecordTermQuery.spatialPowerBound_binary hn ht ha)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordBankProducts.common
  CoefficientMarkedRecordBankProducts.cofactor

/-- This bounds the actual fixed clearing recipe, including its creating odd
power, independently of prefix, AUX and radius. -/
theorem spatial_degree (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (i : ℕ) (hi : i < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8) :
    (polynomial hn ht ha ctx k hk i).totalDegree ≤ spatialDegree hn ht ha ctx := by
  have hp : UniformIntegralPowerSchedule.birth
      (CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx k hk).horizon
      (2^(CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx k hk).width) i ≤
      CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx := by
    dsimp only [CoefficientMarkedRecordTermQuery.arguments, CoefficientMarkedRecordTermQuery.pack]
    unfold CoefficientMarkedRecordTermQuery.spatialPowerBound
    apply UniformIntegralPowerSchedule.birth_le
    change i ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1
    have hb := CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk
    rw [CoefficientMarkedPreludeActual.indices_length] at hb
    omega
  unfold polynomial CoefficientBankLeafQuery.polynomial
  split_ifs
  · exact (physical_degree _ _ _ _ _ _).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (degree_le_cap hn ht ha ctx i hi)) hp)
  · rw [MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

end LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
