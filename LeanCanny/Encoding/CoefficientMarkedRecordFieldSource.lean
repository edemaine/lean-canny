/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordBankSource
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityRadiusHeight
/-! # The installed field source is an original bounded parameter polynomial -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def root (z : List Bool) := pairFst (IntegralMixedPhysicalFieldEquality.context false z)

def selected (z : List Bool) : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (root z)) :=
  ⟨IntegralMixedPhysicalFieldEquality.catalogSelected n false z,
    IntegralMixedPhysicalFieldEquality.newest_lt _ _ (by
      change 0 < IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (root z)
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
      omega)⟩

noncomputable def polynomial (z : List Bool) : Polynomial ℤ[X] :=
  CoefficientMarkedRecordBankSource.polynomial hn ht ha (root z) (selected (n := n) z)

theorem oldArgument_packet (z : List Bool) :
    IntegralMixedPhysicalFieldEquality.catalogOldArgument n z =
      CoefficientMarkedRecordBankSource.packet (n := n) (root z) (selected (n := n) z).val := by
  unfold IntegralMixedPhysicalFieldEquality.catalogOldArgument IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
    CoefficientMarkedRecordBankSource.packet CoefficientMarkedRecordRowLayout.key
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

attribute [local irreducible] CoefficientMarkedRecordBankSource.polynomial
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedFramedHistoryFamilyBits.family

/-- Both native probes use this same constructed left characteristic source. -/
theorem specializes {R : List Bool → ℕ} (hR : BinaryFn R) (z : List Bool)
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (root z) ≤ R (root z)) :
    (polynomial hn ht ha z).map (evalRingHom ((2 : ℤ) ^ R (root z))) =
      (IntegralMixedPhysicalFieldEquality.originalSource hn ht ha hR).polynomial
        (IntegralMixedPhysicalFieldEquality.oldArgument hn ht ha hR z) := by
  rw [IntegralMixedPhysicalFieldEquality.old_polynomial_base, oldArgument_packet]
  exact CoefficientMarkedRecordBankSource.specializes hn ht ha (root z) R hC (selected (n := n) z)

theorem derivative_specializes {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool)
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (root z) ≤ R (root z)) (k : ℕ) :
    (Polynomial.derivative^[k] (polynomial hn ht ha z)).map (evalRingHom ((2 : ℤ) ^ R (root z))) =
      (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha hR).polynomial
        (IntegralMixedPhysicalFieldEquality.probe hn ht ha hR right (pair z (BinaryNatCode.encode k))) := by
  rw [← Polynomial.iterate_derivative_map, specializes hn ht ha hR z hC]
  rw [IntegralMixedPhysicalFieldEquality.derivative_polynomial_base,
    IntegralMixedPhysicalFieldEquality.old_polynomial_base]

noncomputable def coefficientBudget (z : List Bool) : ℕ :=
  IntegerPolynomialDyadic.massBudget
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (root z))
    (IntegralMixedPhysicalFieldEquality.fieldSlope hn ht ha (root z))
    (IntegralMixedPhysicalFieldEquality.fieldOffset hn ht ha (root z))

theorem root_FP : root ∈ FP := mem_FP_comp (IntegralMixedPhysicalFieldEquality.context_FP false) pairFst_mem_FP

theorem coefficientBudget_binary : BinaryFn (coefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp root_FP)
    ((IntegralMixedPhysicalFieldEquality.fieldSlope_binary hn ht ha).comp root_FP)
    ((IntegralMixedPhysicalFieldEquality.fieldOffset_binary hn ht ha).comp root_FP)

theorem target_degree (z : List Bool) :
    (polynomial hn ht ha z).natDegree ≤ IntegralMixedPhysicalFieldEquality.catalogDegree hn ht ha (root z) := by
  unfold polynomial CoefficientMarkedRecordBankSource.polynomial CoefficientMarkedRecordBankPolynomial.polynomial
  apply (CoefficientMarkedRecordBankPolynomial.formal_degree _ _).trans_eq
  rw [CoefficientMarkedRecordBankSource.birth_eq]
  rfl

/-- Native evaluated heights bound every coefficient of the constructed parameter source. -/
theorem coefficient_degree_mass (z : List Bool) (j : ℕ) :
    ((polynomial hn ht ha z).coeff j).natDegree ≤ IntegralMixedPhysicalFieldEquality.fieldSlope hn ht ha (root z) ∧
      coefficientMass ((polynomial hn ht ha z).coeff j) ≤ 2 ^ coefficientBudget hn ht ha z := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := specializes hn ht ha (BinaryFn.const r) z hr
  have HC := congrArg (fun p : ℤ[X] => p.coeff j) HS
  rw [Polynomial.coeff_map] at HC
  change ((polynomial hn ht ha z).coeff j).eval ((2 : ℤ) ^ r) = _ at HC
  rw [HC]
  exact (coeff_natAbs_le_coefficientMass _ j).trans
    (IntegralMixedPhysicalFieldEquality.source_mass hn ht ha (BinaryFn.const r) z)

noncomputable def derivativeBudget (z : List Bool) : ℕ :=
  IntegerPolynomialDyadic.massBudget
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (root z))
    (IntegralMixedPhysicalFieldEquality.fieldSlope hn ht ha (root z))
    (IntegralMixedPhysicalFieldEquality.derivativeOffset hn ht ha (root z))

theorem derivativeBudget_binary : BinaryFn (derivativeBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp root_FP)
    ((IntegralMixedPhysicalFieldEquality.fieldSlope_binary hn ht ha).comp root_FP)
    ((IntegralMixedPhysicalFieldEquality.derivativeOffset_binary hn ht ha).comp root_FP)

theorem derivative_coefficient_degree_mass (z : List Bool) (k j : ℕ) :
    ((Polynomial.derivative^[k] (polynomial hn ht ha z)).coeff j).natDegree ≤
      IntegralMixedPhysicalFieldEquality.fieldSlope hn ht ha (root z) ∧
      coefficientMass ((Polynomial.derivative^[k] (polynomial hn ht ha z)).coeff j) ≤
        2 ^ derivativeBudget hn ht ha z := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := derivative_specializes hn ht ha (BinaryFn.const r) false z hr k
  have HC := congrArg (fun p : ℤ[X] => p.coeff j) HS
  rw [Polynomial.coeff_map] at HC
  change ((Polynomial.derivative^[k] (polynomial hn ht ha z)).coeff j).eval ((2 : ℤ) ^ r) = _ at HC
  rw [HC]
  exact (coeff_natAbs_le_coefficientMass _ j).trans
    (IntegralMixedPhysicalFieldEquality.derivative_mass hn ht ha (BinaryFn.const r) false z k)

end LeanCanny.Encoding.CoefficientMarkedRecordFieldSource
