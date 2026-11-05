/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordPrefixBankSource
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankQueryHeight
/-! # The actual prepared-parent characteristic is an original parameter family -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalBankSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedPhysicalCriticalBankEquality (fieldSlope fieldOffset derivativeOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev stage (q : List Bool) := IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q) - 1
abbrev birth (n : List Bool → ℕ) (q : List Bool) :=
  (CoefficientMarkedPreludeActual.indices n (IntegralMixedPhysicalCriticalQuery.root q)).length +
    (CoefficientMarkedRecordActual.codes (IntegralMixedPhysicalCriticalQuery.root q) (stage q)).length

theorem parent_key (n : List Bool → ℕ) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    IntegralMixedPhysicalCriticalPrefixes.key n false false q =
      CoefficientMarkedRecordRowLayout.key (n := n) (IntegralMixedPhysicalCriticalQuery.root q) (stage q) q := by
  unfold IntegralMixedPhysicalCriticalPrefixes.key IntegralMixedPhysicalCriticalPrefixes.birth
    CoefficientMarkedRecordRowLayout.key IntegralMixedPhysicalMarkedPlan.leafCount
  rw [CoefficientMarkedPreludeActual.indices_length]
  simp only [pairFst_pair, Bool.false_eq_true, ite_false]
  unfold stage
  congr 1
  omega

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def polynomial (q : List Bool) (i : Fin (birth n q)) : Polynomial ℤ[X] :=
  CoefficientMarkedRecordBankPolynomial.polynomial hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) (stage q) i

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedFramedHistoryFamilyBits.family
  CoefficientMarkedRecordBankPolynomial.polynomial

/-- The saved parent stays at count-1; the child source is not substituted. -/
theorem specializes {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q)) (i : Fin (birth n q)) :
    (polynomial hn ht ha q i).map (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q))) =
      (IntegralMixedPhysicalCriticalBankEquality.source hn ht ha hR false).polynomial
        (pair q (BinaryNatCode.encode i.val)) := by
  rw [IntegralMixedPhysicalCriticalBankEquality.source_polynomial_base]
  have HP : IntegralMixedPhysicalCriticalBankEquality.catalogArgument n q i.val =
      CoefficientMarkedRecordPrefixBankSource.packet n (IntegralMixedPhysicalCriticalQuery.root q) (stage q) q i.val := by
    unfold IntegralMixedPhysicalCriticalBankEquality.catalogArgument CoefficientMarkedRecordPrefixBankSource.packet
    rw [parent_key n q hc]
  rw [HP]
  exact CoefficientMarkedRecordPrefixBankSource.specializes hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    R (stage q) (Nat.sub_le _ _) q hC i

theorem derivative_specializes {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (birth n q)) (k : ℕ) :
    (Polynomial.derivative^[k] (polynomial hn ht ha q i)).map
      (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q))) =
      (IntegralMixedPhysicalCriticalBankEquality.derivatives hn ht ha hR false).polynomial
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) := by
  rw [← Polynomial.iterate_derivative_map, specializes hn ht ha hR q hc hC,
    IntegralMixedPhysicalCriticalBankEquality.derivative_polynomial]

noncomputable def coefficientBudget (q : List Bool) :=
  IntegerPolynomialDyadic.massBudget
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
    (fieldSlope hn ht ha q) (fieldOffset hn ht ha q)

theorem coefficientBudget_binary : BinaryFn (coefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp pairFst_mem_FP)
    (IntegralMixedPhysicalCriticalBankEquality.fieldSlope_binary hn ht ha)
    (IntegralMixedPhysicalCriticalBankEquality.fieldOffset_binary hn ht ha)

theorem coefficient_degree_mass (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (birth n q)) (j : ℕ) :
    ((polynomial hn ht ha q i).coeff j).natDegree ≤ fieldSlope hn ht ha q ∧
      coefficientMass ((polynomial hn ht ha q i).coeff j) ≤ 2 ^ coefficientBudget hn ht ha q := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := specializes hn ht ha (BinaryFn.const r) q hc hr i
  have HE := congrArg (fun p : ℤ[X] => p.coeff j) HS
  rw [Polynomial.coeff_map] at HE
  change ((polynomial hn ht ha q i).coeff j).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE]
  exact (coeff_natAbs_le_coefficientMass _ j).trans
    (IntegralMixedPhysicalCriticalBankEquality.source_mass hn ht ha (BinaryFn.const r) q i.val)

noncomputable def derivativeBudget (q : List Bool) :=
  IntegerPolynomialDyadic.massBudget
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
    (fieldSlope hn ht ha q) (derivativeOffset hn ht ha q)

theorem derivativeBudget_binary : BinaryFn (derivativeBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp pairFst_mem_FP)
    (IntegralMixedPhysicalCriticalBankEquality.fieldSlope_binary hn ht ha)
    (IntegralMixedPhysicalCriticalBankEquality.derivativeOffset_binary hn ht ha)

theorem derivative_coefficient_degree_mass (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (birth n q)) (k j : ℕ) :
    ((Polynomial.derivative^[k] (polynomial hn ht ha q i)).coeff j).natDegree ≤ fieldSlope hn ht ha q ∧
      coefficientMass ((Polynomial.derivative^[k] (polynomial hn ht ha q i)).coeff j) ≤
        2 ^ derivativeBudget hn ht ha q := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := derivative_specializes hn ht ha (BinaryFn.const r) q hc hr i k
  have HE := congrArg (fun p : ℤ[X] => p.coeff j) HS
  rw [Polynomial.coeff_map] at HE
  change ((Polynomial.derivative^[k] (polynomial hn ht ha q i)).coeff j).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE]
  exact (coeff_natAbs_le_coefficientMass _ j).trans
    (IntegralMixedPhysicalCriticalBankEquality.derivative_mass hn ht ha (BinaryFn.const r) q i.val k)

end LeanCanny.Encoding.CoefficientMarkedCriticalBankSource
