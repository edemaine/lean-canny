/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldPhysical
/-! # Critical-bank comparisons use their literal own full physical columns -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalBankQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem scalarAt_map {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (D : CoefficientMarkedRecordRows.Data R) (i : ℕ) :
    CoefficientMarkedRecordFieldQuery.scalarAt (CoefficientMarkedRecordRows.map φ D) i =
      CoefficientMarkedRecordFieldQuery.scalarAt D i := rfl

private theorem lookup_column (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool → List Bool)
    (coordinate : (c d : List Bool) → Fin ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c)))
    (c d : List Bool) :
    CoefficientMarkedRecordFieldQuery.scalarAt (CoefficientMarkedRecordRowBounds.samplerData P D H (key c))
      (coordinate c d).val = (IntegralFramedPhysicalUnivariateTest.column P D H key coordinate c d).val := by
  simp only [CoefficientMarkedRecordFieldQuery.scalarAt, CoefficientMarkedRecordRowBounds.samplerData,
    dite_eq_left (coordinate c d).isLt]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def column (child : Bool) (q : List Bool) (i : ℕ) : ℕ :=
  CoefficientMarkedRecordFieldQuery.scalarAt
    (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q) (Nat.sub_le _ _)) (selected n child q i)

noncomputable def physical (child : Bool) (q : List Bool)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) : MvPolynomial ℕ ℤ[X] :=
  (polynomial hn ht ha child q i k).toMvPolynomial (column hn ht ha child q i.val)

private noncomputable def nativeData {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool) :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  CoefficientMarkedRecordRowBounds.samplerData B.parameters B.plan B.data
    (IntegralMixedPhysicalCriticalPrefixes.key n false child q)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedFramedHistoryFamilyBits.family CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedRecordRowBounds.samplerData

private theorem nativeData_eq {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    CoefficientMarkedRecordRows.indexed hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) R (stage child q) q =
      nativeData hn ht ha hR child q := by
  have HE := CoefficientMarkedRecordRowBounds.certifiedIndexed_eq hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root q) hR (stage child q) q
  unfold CoefficientMarkedRecordRowBounds.certifiedIndexed at HE
  rw [← prefix_key n child q hc] at HE
  exact HE.symm

theorem column_specializes {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q)) (i k : ℕ) :
    let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
    column hn ht ha child q i =
      (IntegralFramedPhysicalUnivariateTest.column B.parameters B.plan B.data
        (IntegralMixedPhysicalCriticalPrefixes.key n false child)
        (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR false child) q
        (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))).val := by
  dsimp only
  have HM := congrArg (fun D : CoefficientMarkedRecordRows.Data ℤ =>
    CoefficientMarkedRecordFieldQuery.scalarAt D (selected n child q i))
    (CoefficientMarkedRecordRows.map_indexed hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) R
      (stage child q) (Nat.sub_le _ _) q hC)
  rw [scalarAt_map, nativeData_eq hn ht ha hR child q hc] at HM
  have HM' : column hn ht ha child q i = CoefficientMarkedRecordFieldQuery.scalarAt
      (nativeData hn ht ha hR child q) (selected n child q i) := HM
  apply HM'.trans
  let J := IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR false child q
    (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))
  have HJ : J.val = selected n child q i := by
    simp only [J, IntegralMixedPhysicalCriticalBankEquality.coordinate, IntegralMixedPhysicalCriticalBankEquality.selected,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, selected]
  rw [← HJ]
  exact lookup_column _ _ _ _ _ _ _

noncomputable def nativePhysical {R : List Bool → ℕ} (hR : BinaryFn R)
    (child : Bool) (q : List Bool) (i k : ℕ) : MvPolynomial ℕ ℤ :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  MvPolynomial.rename Fin.val
    (((IntegralMixedPhysicalCriticalBankEquality.querySource hn ht ha hR child).polynomial
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))).toMvPolynomial
      (IntegralFramedPhysicalUnivariateTest.column B.parameters B.plan B.data
        (IntegralMixedPhysicalCriticalPrefixes.key n false child)
        (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR false child) q
        (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))

/-- The full physical column belongs to this OWN parent/child sampler. -/
theorem physical_specializes {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    MvPolynomial.map (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q)))
      (physical hn ht ha child q i k) = nativePhysical hn ht ha hR child q i.val k := by
  unfold physical nativePhysical
  rw [RelativeValueSystemMap.coordinate, specializes hn ht ha hR child q hc hC i k,
    MvPolynomial.rename_toMvPolynomial, column_specializes hn ht ha hR child q hc hC i.val k]

theorem physical_coefficient_degree_mass (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) (v : ℕ →₀ ℕ) :
    ((physical hn ht ha child q i k).coeff v).natDegree ≤
      IntegralMixedPhysicalCriticalBankEquality.querySlope hn ht ha q ∧
    coefficientMass ((physical hn ht ha child q i k).coeff v) ≤ 2 ^ coefficientBudget hn ht ha q := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := physical_specializes hn ht ha (BinaryFn.const r) child q hc hr i k
  have HE := congrArg (fun p : MvPolynomial ℕ ℤ => p.coeff v) HS
  rw [MvPolynomial.coeff_map] at HE
  change ((physical hn ht ha child q i k).coeff v).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE]
  apply (MvMass.coeff_le _ v).trans
  unfold nativePhysical
  apply (MvMass.rename_le _ _).trans
  exact IntegralMixedPhysicalCriticalBankEquality.physical_query_mass hn ht ha (BinaryFn.const r) child q i.val k

theorem physical_degree (child : Bool) (q : List Bool)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    (physical hn ht ha child q i k).totalDegree ≤
      (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q) * power hn ht ha child q i.val :=
  (UnivariateInfinity.degree_le _ _).trans (target_degree hn ht ha child q i k)

end LeanCanny.Encoding.CoefficientMarkedCriticalBankQuery
