/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullQuery
public import LeanCanny.Encoding.IntegralMixedPhysicalPointEquality
/-! # The actual two-physical-power equality query over the parameter -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem planned (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (L F C : List Bool → ℕ) (key : List Bool → List Bool) (a b i : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFramedPointEqualityBits.polynomial (IntegralMixedFramedNormalizationBits.planned P L F C) T key a b i q =
      IntegralMixedFramedPointEqualityBits.polynomial P T key a b i q := rfl

private theorem tables_heq (P : Parameters) (T U : IntegralMixedHeaderTablesBits.Tables) (h : T = U)
    (key : List Bool → List Bool) (a b i : List Bool → ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedPointEqualityBits.polynomial P T key a b i q)
      (IntegralMixedFramedPointEqualityBits.polynomial P U key a b i q) := by
  cases h
  rfl

private noncomputable def expression (N l r a b : ℕ) : MvPolynomial (Fin N) ℤ :=
  CoefficientCriticalCorrelationQuery.monomial N l a 1-CoefficientCriticalCorrelationQuery.monomial N r b 1

private theorem expression_heq {N M : ℕ} (l r a b l' r' a' b' : ℕ)
    (hN : N = M) (hl : l = l') (hr : r = r') (ha : a = a') (hb : b = b') :
    HEq (expression N l r a b) (expression M l' r' a' b') := by
  cases hN
  cases hl
  cases hr
  cases ha
  cases hb
  rfl

private theorem native_expression (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool → List Bool) (a b i : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFramedPointEqualityBits.polynomial P T key a b i q =
      expression (IntegralMixedFramedCriticalGuardBits.count P T key q)
        (IntegralMixedFramedPointEqualityBits.column P T key i a q) (IntegralMixedFramedPointEqualityBits.column P T key i b q)
        (IntegralMixedFramedCriticalGuardBits.physicalPower P key a q) (IntegralMixedFramedCriticalGuardBits.physicalPower P key b q) := rfl

private theorem constants (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool → List Bool) (a b i : List Bool → ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedPointEqualityBits.polynomial P T key a b i q)
      (IntegralMixedFramedPointEqualityBits.polynomial P T (fun _ => key q) (fun _ => a q) (fun _ => b q) (fun _ => i q) []) := by
  have HL := native_expression P T key a b i q
  have HR := native_expression P T (fun _ => key q) (fun _ => a q) (fun _ => b q) (fun _ => i q) []
  have HE := expression_heq (N := IntegralMixedFramedCriticalGuardBits.count P T key q)
    (M := IntegralMixedFramedCriticalGuardBits.count P T (fun _ => key q) [])
    (IntegralMixedFramedPointEqualityBits.column P T key i a q) (IntegralMixedFramedPointEqualityBits.column P T key i b q)
    (IntegralMixedFramedCriticalGuardBits.physicalPower P key a q) (IntegralMixedFramedCriticalGuardBits.physicalPower P key b q)
    _ _ _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  exact (heq_of_eq HL).trans (HE.trans (heq_of_eq HR.symm))

private theorem constants_heq (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key key' : List Bool) (a b i a' b' i' : ℕ) (hk : key = key') (ha : a = a') (hb : b = b') (hi : i = i') :
    HEq (IntegralMixedFramedPointEqualityBits.polynomial P T (fun _ => key) (fun _ => a) (fun _ => b) (fun _ => i) [])
      (IntegralMixedFramedPointEqualityBits.polynomial P T (fun _ => key') (fun _ => a') (fun _ => b') (fun _ => i') []) := by
  cases hk
  cases ha
  cases hb
  cases hi
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def key (ctx : List Bool) := CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) []

noncomputable def raw (ctx : List Bool) (a b i : ℕ) :
    MvPolynomial (Fin (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) [] 0).count) ℤ :=
  IntegralMixedFramedPointEqualityBits.polynomial (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (fun _ => key (n := n) ctx) (fun _ => a) (fun _ => b) (fun _ => i) []

noncomputable def integer (ctx : List Bool) (a b i : ℕ) :
    MvPolynomial (Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count) ℤ :=
  MvPolynomial.rename (Fin.cast (CoefficientMarkedRecordCriticalFullQuery.count_eq hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] 0))
    (raw hn ht ha ctx a b i)

noncomputable def polynomial (ctx : List Bool) (a b i : ℕ) := MvPolynomial.map (Polynomial.C : ℤ →+* ℤ[X]) (integer hn ht ha ctx a b i)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.tables
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data IntegralMixedAuxiliaryMarkedIntegerPlan.seed

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

theorem native_key (ctx aux : List Bool) : (B).key (pair ctx aux) = key (n := n) ctx := by
  change IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (pair ctx aux) = _
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, key, CoefficientMarkedRecordRowLayout.key,
    CoefficientMarkedPreludeActual.indices_length, pairFst_pair, IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]

theorem raw_native (ctx : List Bool) (a b i : ℕ) :
    HEq (raw hn ht ha ctx a b i)
      (IntegralMixedFramedPointEqualityBits.polynomial (B).parameters (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (fun _ => key (n := n) ctx) (fun _ => a) (fun _ => b) (fun _ => i) []) := by
  have HP := planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (fun _ => key (n := n) ctx) (fun _ => a) (fun _ => b) (fun _ => i) []
  have HT := tables_heq (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR).symm
    (fun _ => key (n := n) ctx) (fun _ => a) (fun _ => b) (fun _ => i) []
  exact (heq_of_eq HP.symm).trans HT

theorem raw_packet (ctx aux : List Bool) (a b i : ℕ) :
    HEq (raw hn ht ha ctx a b i)
      (IntegralMixedFramedPointEqualityBits.polynomial (B).parameters (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralMixedPhysicalPointEquality.left
        IntegralMixedPhysicalPointEquality.right IntegralMixedPhysicalPointEquality.coordinate
        (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i))) := by
  have HK : IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key
      (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i)) = key (n := n) ctx := by
    simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum, pairFst_pair]
    exact native_key hn ht ha hR ctx aux
  have HF := IntegralMixedPhysicalPointEquality.datum_fields (pair ctx aux) a b i
  have HC := constants (B).parameters (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralMixedPhysicalPointEquality.left
    IntegralMixedPhysicalPointEquality.right IntegralMixedPhysicalPointEquality.coordinate
    (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i))
  have HE := constants_heq (B).parameters (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    _ _ _ _ _ _ _ _ HK HF.1 HF.2.1 HF.2.2
  exact (raw_native hn ht ha hR ctx a b i).trans (HE.symm.trans HC.symm)

end LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
