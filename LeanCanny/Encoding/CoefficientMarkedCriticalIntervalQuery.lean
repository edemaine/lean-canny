/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermBounds
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
/-! # Literal lower and upper interval queries at the prepared full child -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalIntervalQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def physicalQuery (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (w : List Bool → List Bool) (key : List Bool) :=
  MvPolynomial.rename (IntegralFramedPhysicalSquare.sampler P D H key).scalar
    (IntegralMixedFramedBankTermBits.polynomial P D H w key)

private theorem native_planned (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) (w : List Bool → List Bool) :
    HEq (MvPolynomial.rename
      (IntegralFramedPhysicalSquare.sampler (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
        (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key).scalar
      (IntegralMixedFramedBankTermBits.polynomial (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
        (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) w key))
      (MvPolynomial.rename (IntegralFramedPhysicalSquare.sampler P D H key).scalar
        (IntegralMixedFramedBankTermBits.polynomial P D H w key)) := HEq.rfl

/-- The full child uses all original records, including the reserved probe. -/
theorem child_key (n : List Bool → ℕ) (q : List Bool) :
    IntegralMixedPhysicalCriticalPrefixes.key n false true q =
      CoefficientMarkedRecordRowLayout.key (n := n) (IntegralMixedPhysicalCriticalQuery.root q)
        (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) q := by
  unfold IntegralMixedPhysicalCriticalPrefixes.key IntegralMixedPhysicalCriticalPrefixes.birth
    CoefficientMarkedRecordRowLayout.key IntegralMixedPhysicalMarkedPlan.leafCount
  rw [CoefficientMarkedPreludeActual.indices_length]
  simp only [pairFst_pair, Bool.false_eq_true, ite_false, ite_true, Nat.sub_zero]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def polynomial (upper : Bool) (ctx : List Bool) :=
  CoefficientMarkedRecordTermQuery.polynomial hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false upper)
    ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalSquare.sampler IntegralMixedFramedBankTermBits.polynomial
  IntegralMixedPhysicalMarkedPlan.bank CoefficientMarkedRecordTermQuery.polynomial physicalQuery

theorem specializes (upper : Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q)) :
    let B := IntegralMixedPhysicalCriticalInterval.childBank hn ht ha hR false
    let key := B.key q
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q)))
      (polynomial hn ht ha upper (IntegralMixedPhysicalCriticalQuery.root q)))
      (physicalQuery B.parameters B.plan B.data
        (IntegralMixedPhysicalCriticalInterval.word n false upper) key) := by
  dsimp only
  unfold polynomial
  have HS := CoefficientMarkedRecordTermQuery.polynomial_specialize hn ht ha
    (IntegralMixedPhysicalCriticalInterval.word n false upper) (IntegralMixedPhysicalCriticalQuery.root q)
    R (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl q hC
  rw [← child_key] at HS
  unfold physicalQuery IntegralMixedPhysicalCriticalInterval.childBank IntegralMixedPhysicalMarkedPlan.bank
  exact HS.trans (native_planned (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (IntegralMixedPhysicalCriticalPrefixes.key n false true q)
    (IntegralMixedPhysicalCriticalInterval.word n false upper)).symm

/-- The native endpoint-difference term keeps its original coefficient budgets. -/
theorem coefficient_degree_mass (upper : Bool) (ctx : List Bool)
    (v : Fin (CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).dimension →₀ ℕ) :
    ((polynomial hn ht ha upper ctx).coeff v).natDegree ≤
      CoefficientMarkedRecordTermQuery.slope hn ht ha (IntegralMixedPhysicalCriticalInterval.word n false upper) ctx ∧
    coefficientMass ((polynomial hn ht ha upper ctx).coeff v) ≤
      2 ^ CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha
        (IntegralMixedPhysicalCriticalInterval.word n false upper) ctx :=
  CoefficientMarkedRecordTermQuery.coefficient_degree_mass hn ht ha
    (IntegralMixedPhysicalCriticalInterval.word n false upper) ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl v

theorem budget_binary (upper : Bool) : BinaryFn (CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha
    (IntegralMixedPhysicalCriticalInterval.word n false upper)) :=
  CoefficientMarkedRecordTermQuery.coefficientBudget_binary hn ht ha
    (IntegralMixedPhysicalCriticalInterval.word n false upper) (IntegralMixedPhysicalCriticalInterval.word_FP hn false upper)

end LeanCanny.Encoding.CoefficientMarkedCriticalIntervalQuery
