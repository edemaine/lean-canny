/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordRowDegree
/-! # Original spatial degree of the actual critical-correlation queries -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientCriticalCorrelationQuery
open LeanCanny.Encoding Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem le_succ_mul (a b : ℕ) : b ≤ (a + 1) * b := by
  calc
    b ≤ a * b + b := Nat.le_add_left _ _
    _ = (a + 1) * b := by rw [Nat.add_mul, Nat.one_mul]

private theorem monomial_degree {R : Type*} [CommRing R] (N i w : ℕ) (a : R) :
    (monomial N i w a).totalDegree ≤ w := by
  unfold monomial
  split_ifs
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp only [MvPolynomial.totalDegree_zero, Nat.zero_le]

/-- Changing only the ambient count keeps the actual sparse recipe bounded,
including clipped columns and every inactive or out-of-range stage. -/
theorem native_count_degree {R : Type*} [CommRing R]
    (P : IntegralCriticalHistoryTask.Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool) (stage count : ℕ) (d : R) :
    (polynomial {nativeMetadata P T key stage with count := count} d).totalDegree ≤
      IntegralMixedFramedPhysicalRowDegree.upper P (pairFst key) := by
  unfold polynomial
  split_ifs with ha
  · have hactive : IntegralMixedFramedCriticalGuardBits.Active P T (fun _ => key) (fun _ => stage) [] := by
      change decide (IntegralMixedFramedCriticalGuardBits.Active P T (fun _ => key) (fun _ => stage) []) = true at ha
      exact of_decide_eq_true ha
    let S := P.cap (pairFst key) + 1
    let N := 2 ^ P.width (pairFst key)
    have hm : stage ≤ S := hactive.1.le.trans (min_le_right _ _)
    have hs := UniformIntegralPowerSchedule.birth_le S N stage hm
    have hp := UniformIntegralPowerSchedule.physical_le S N stage (hm.trans (Nat.le_succ _))
    have hb : UniformIntegralPowerSchedule.birth S N S ≤
        (2 * UniformIntegralPowerSchedule.cap S N + 1) * UniformIntegralPowerSchedule.birth S N S := by
      exact le_succ_mul (2 * UniformIntegralPowerSchedule.cap S N) (UniformIntegralPowerSchedule.birth S N S)
    have hu : (2 * UniformIntegralPowerSchedule.cap S N + 1) * UniformIntegralPowerSchedule.birth S N S ≤
        IntegralMixedFramedPhysicalRowDegree.upper P (pairFst key) := by
      unfold IntegralMixedFramedPhysicalRowDegree.upper
      exact le_succ_mul (N + P.degree (pairFst key))
        ((2 * UniformIntegralPowerSchedule.cap S N + 1) * UniformIntegralPowerSchedule.birth S N S)
    apply (MvPolynomial.totalDegree_sub _ _).trans
    exact max_le ((monomial_degree _ _ _ _).trans (hs.trans (hb.trans hu)))
      ((monomial_degree _ _ _ _).trans (hp.trans hu))
  · exact Nat.zero_le _

end LeanCanny.Algebra.CoefficientCriticalCorrelationQuery

namespace LeanCanny.Encoding.CoefficientMarkedRecordCriticalDegree
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- The existing original row ceiling also bounds ALL actual correlation queries. -/
theorem polynomial_degree (ctx : List Bool) (k : ℕ) (aux : List Bool) (stage : ℕ) :
    (CoefficientMarkedRecordCriticalQuery.polynomial hn ht ha ctx k aux stage).totalDegree ≤
      CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx := by
  have hh := CoefficientCriticalCorrelationQuery.native_count_degree
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) stage
    (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).count
    (CoefficientMarkedRecordBankDenominator.polynomial hn ht ha ctx k
      (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).age)
  simpa only [CoefficientMarkedRecordCriticalQuery.polynomial, CoefficientMarkedRecordCriticalQuery.metadata,
    CoefficientMarkedRecordRowLayout.key_root, CoefficientMarkedRecordRowDegree.spatialDegree] using hh

end LeanCanny.Encoding.CoefficientMarkedRecordCriticalDegree
