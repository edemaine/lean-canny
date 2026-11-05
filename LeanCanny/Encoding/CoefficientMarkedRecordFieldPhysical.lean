/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
/-! # The formal field query uses its actual complete physical scalar column -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedPhysicalFieldEquality (context catalogSelected contextProbe)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def scalarAt {R : Type*} [CommRing R] (d : CoefficientMarkedRecordRows.Data R) (i : ℕ) : ℕ :=
  if hi : i < d.birth then (d.scalar ⟨i, hi⟩).val else 0

private theorem scalarAt_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (d : CoefficientMarkedRecordRows.Data R) (i : ℕ) :
    scalarAt (CoefficientMarkedRecordRows.map φ d) i = scalarAt d i := rfl

private noncomputable def indexedData (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : CoefficientMarkedRecordRows.Data ℤ :=
  ⟨IntegralFramedPhysicalSquare.count P D key, (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key,
    (IntegralFramedPhysicalSquare.sampler P D H key).rows, (IntegralFramedPhysicalSquare.sampler P D H key).scalar⟩

private theorem indexedData_planned (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    indexedData (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key = indexedData P D H key := rfl

private theorem lookup_column (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool → List Bool)
    (coordinate : (c d : List Bool) → Fin ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c)))
    (c d : List Bool) : scalarAt (indexedData P D H (key c)) (coordinate c d).val =
      (IntegralFramedPhysicalUnivariateTest.column P D H key coordinate c d).val := by
  simp only [scalarAt, indexedData, dite_eq_left (coordinate c d).isLt]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def column (right : Bool) (z : List Bool) : ℕ :=
  scalarAt (CoefficientMarkedRecordRows.symbolic hn ht ha (rightRoot right z)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) le_rfl) (catalogSelected n right z)

noncomputable def physical (right : Bool) (z : List Bool) (k : ℕ) : MvPolynomial ℕ ℤ[X] :=
  (polynomial hn ht ha right z k).toMvPolynomial (column hn ht ha right z)

private theorem physical_full_key (c : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c)
      (IntegralMixedCausalRecordPlanBits.count (pairFst c)) [] =
      IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c := by
  unfold CoefficientMarkedRecordRowLayout.key IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family
  CoefficientMarkedRecordRows.symbolic

private noncomputable def nativeData {R : List Bool → ℕ} (hR : BinaryFn R) (c : List Bool) :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  indexedData B.parameters B.plan B.data (B.key c)

private theorem nativeData_base {R : List Bool → ℕ} (hR : BinaryFn R) (c : List Bool) :
    nativeData hn ht ha hR c = indexedData (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c) := by
  have HB : IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR := rfl
  simp only [nativeData, HB, IntegralMixedAuxiliaryMarkedRecordPlan.bank]
  exact indexedData_planned _ _ _ _ _ _ _

private theorem physical_selected_context {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ) :
    (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hR (context right z)
      (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
        (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k)))).val =
      catalogSelected n right z := by
  simp only [IntegralMixedPhysicalFieldEquality.coordinate, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [IntegralMixedPhysicalFieldEquality.count_catalog]
  apply min_eq_left
  have HI := IntegralMixedPhysicalFieldEquality.newest_lt
    (IntegralMixedPhysicalFieldEquality.catalogCount n (context right z)) (IntegralMixedPhysicalFieldEquality.label right z)
    (by unfold IntegralMixedPhysicalFieldEquality.catalogCount IntegralMixedAuxiliaryMarkedRecordPlan.fullCount; omega)
  change catalogSelected n right z < IntegralMixedPhysicalFieldEquality.catalogCount n (context right z) at HI
  omega

theorem column_specializes {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ)
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ R (rightRoot right z)) :
    column hn ht ha right z =
      (IntegralFramedPhysicalUnivariateTest.column
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).data
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key
        (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hR) (context right z)
        (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
          (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k)))).val := by
  have HM := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ => scalarAt d (catalogSelected n right z))
    (CoefficientMarkedRecordRows.map_indexed hn ht ha (rightRoot right z) R
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) le_rfl [] hC)
  have HD : CoefficientMarkedRecordRows.indexed hn ht ha (rightRoot right z) R
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) [] = nativeData hn ht ha hR (context right z) := by
    rw [nativeData_base]
    unfold CoefficientMarkedRecordRows.indexed
    rw [show rightRoot right z = pairFst (context right z) from rfl, physical_full_key]
    rfl
  rw [scalarAt_map, HD] at HM
  have HM' : column hn ht ha right z = scalarAt (nativeData hn ht ha hR (context right z))
      (catalogSelected n right z) := HM
  apply HM'.trans
  let i := IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hR (context right z)
    (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
      (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k)))
  have HI : i.val = catalogSelected n right z := physical_selected_context hn ht ha hR right z k
  calc
    _ = scalarAt (nativeData hn ht ha hR (context right z)) i.val := congrArg _ HI.symm
    _ = _ := lookup_column _ _ _ _ _ _ _

theorem physical_specializes (r : ℕ) (right : Bool) (z : List Bool) (k : ℕ)
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (CoefficientMarkedRecordFieldSource.root z) ≤ r)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ r) :
    MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) (physical hn ht ha right z k) =
      MvPolynomial.rename Fin.val
        (((IntegralMixedPhysicalFieldEquality.querySource hn ht ha (BinaryFn.const r)).polynomial (contextProbe n right z k)).toMvPolynomial
          (IntegralFramedPhysicalUnivariateTest.column
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (BinaryFn.const r) false).parameters
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (BinaryFn.const r) false).plan
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (BinaryFn.const r) false).data
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (BinaryFn.const r) false).key
            (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha (BinaryFn.const r)) (context right z)
            (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
              (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k))))) := by
  rw [physical, RelativeValueSystemMap.coordinate, specializes hn ht ha r right z k hL hR,
    MvPolynomial.rename_toMvPolynomial, column_specializes hn ht ha (BinaryFn.const r) right z k hR]

end LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
