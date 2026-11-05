/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankIncidence
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Actual critical-bank queries in their OWN finite raw-variable space -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalBankVariables
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem input_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (hp : ∀ c, 0 < (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
    (q : List Bool) : (IntegralFramedPhysicalSquare.input P D H L F C hs key hp).count q =
      IntegralFramedPhysicalSquare.count P D (key q) := rfl

private theorem planned_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralFramedPhysicalSquare.count (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key =
      IntegralFramedPhysicalSquare.count P D key := rfl

private theorem toMv_variables {R : Type*} [CommRing R] (p : R[X]) (c N : ℕ) (hc : c < N) :
    ∀ v ∈ (p.toMvPolynomial c).vars, v < N := by
  intro v hv
  rw [← MvPolynomial.rename_toMvPolynomial (fun _ : Unit => c) () p] at hv
  obtain ⟨j, _, rfl⟩ := MvPolynomial.mem_vars_rename (fun _ : Unit => c) (p.toMvPolynomial ()) hv
  exact hc

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def count (child : Bool) (q : List Bool) :=
  (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count

private theorem count_eq {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child).count q = count hn ht ha child q := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  have h1 := input_count B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralMixedPhysicalCriticalPrefixes.key n false child)
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha hR false child) q
  have h2 := planned_count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (IntegralMixedPhysicalCriticalPrefixes.key n false child q)
  have h3 := CoefficientMarkedRecordRowLayout.count_eq hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) R
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) q
  rw [← CoefficientMarkedCriticalBankQuery.prefix_key n child q hc] at h3
  exact h1.trans (h2.trans h3)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalMarkedPlan.bank CoefficientMarkedRecordRows.symbolic

/-- The column bound is derived from the literal installed column at an
internally chosen effective radius. No word or root-tuple existence is needed. -/
theorem column_lt (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) (i : ℕ) :
    CoefficientMarkedCriticalBankQuery.column hn ht ha child q i < count hn ht ha child q := by
  let C := CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha (BinaryFn.const C) false
  let j := IntegralFramedPhysicalUnivariateTest.column B.parameters B.plan B.data
    (IntegralMixedPhysicalCriticalPrefixes.key n false child)
    (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha (BinaryFn.const C) false child) q
    (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0))
  have hj := CoefficientMarkedCriticalBankQuery.column_specializes hn ht ha (BinaryFn.const C) child q hc le_rfl i 0
  have hh : j.val < (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (BinaryFn.const C) false child).count q := j.isLt
  rw [← hj] at hh
  exact hh.trans_eq (count_eq hn ht ha (BinaryFn.const C) child q hc)

theorem variable_box (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    ∀ v ∈ (CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k).vars,
      v < count hn ht ha child q := by
  unfold CoefficientMarkedCriticalBankQuery.physical
  exact toMv_variables _ _ _ (column_lt hn ht ha child q hc i.val)

noncomputable def polynomial (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    MvPolynomial (Fin (count hn ht ha child q)) ℤ[X] :=
  CoefficientFinitePhysicalQuery.polynomial _ (CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k)
    (variable_box hn ht ha child q hc i k)

theorem rename_polynomial (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    MvPolynomial.rename Fin.val (polynomial hn ht ha child q hc i k) =
      CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k :=
  CoefficientFinitePhysicalQuery.rename_polynomial _ _ _

theorem degree (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    (polynomial hn ht ha child q hc i k).totalDegree ≤
      (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q) *
        CoefficientMarkedCriticalBankQuery.power hn ht ha child q i.val := by
  unfold polynomial
  rw [CoefficientFinitePhysicalQuery.degree_eq]
  exact CoefficientMarkedCriticalBankQuery.physical_degree hn ht ha child q i k

theorem coefficient_degree_mass (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) (v : Fin (count hn ht ha child q) →₀ ℕ) :
    ((polynomial hn ht ha child q hc i k).coeff v).natDegree ≤
      IntegralMixedPhysicalCriticalBankEquality.querySlope hn ht ha q ∧
    coefficientMass ((polynomial hn ht ha child q hc i k).coeff v) ≤
      2 ^ CoefficientMarkedCriticalBankQuery.coefficientBudget hn ht ha q := by
  apply CoefficientFinitePhysicalQuery.coefficient_degree_mass
  exact CoefficientMarkedCriticalBankQuery.physical_coefficient_degree_mass hn ht ha child q hc i k

/-- The finite polynomial is still the EXACT installed query at its OWN
decoded tuple. All column/finite-variable compatibility is proved internally. -/
theorem value_eq {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w)
    (z : Fin (count hn ht ha child q) → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w hw).val z)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    IntegralMixedPhysicalCriticalBankEquality.value hn ht ha hR false child
      (pair (pair q w) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (SignType.sign
        ((polynomial hn ht ha child q hc i k).eval₂
          (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q))) z)) := by
  rw [CoefficientMarkedCriticalBankIncidence.value_eq hn ht ha hR child q hc hlarge w hw z hz i k]
  unfold polynomial
  rw [CoefficientFinitePhysicalQuery.evaluation]
  rfl

end LeanCanny.Encoding.CoefficientMarkedCriticalBankVariables
