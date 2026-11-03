/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordBank
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordBank
public import LeanCanny.Encoding.IntegralFramedPhysicalLeafSources
/-! # Original native marked and signed-outer physical replay data

Both modes use their actual completed causal record plan. All native
current-Q and header certificates are constructed from original syntax.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

noncomputable def bank (outer : Bool) : IntegralFramedBankQuery.Bank :=if outer then
  IntegralMixedAuxiliaryOuterRecordPlan.bank hn ht ha hR else IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR
noncomputable def native (outer : Bool) : IntegralFramedBankQuery.Access (bank hn ht ha hR outer) :=by
  cases outer
  · exact IntegralMixedAuxiliaryMarkedRecordPlan.bank_access hn ht ha hR
  · exact IntegralMixedAuxiliaryOuterRecordPlan.bank_access hn ht ha hR
noncomputable def controls (outer : Bool) : IntegralMixedFramedCurrentQNativeBits.Controls
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data :=by
  cases outer
  · exact IntegralMixedAuxiliaryMarkedRecordPlan.certifiedControls hn ht ha hR
  · exact IntegralMixedAuxiliaryOuterRecordPlan.certifiedControls hn ht ha hR
noncomputable def tables (outer : Bool) :=(controls hn ht ha hR outer).scalar.tables
theorem tables_native (outer : Bool) : IntegralMixedHeaderTablesBits.Access (tables hn ht ha hR outer) :=
  (controls hn ht ha hR outer).scalar.native
theorem represents (outer : Bool) : IntegralMixedFramedHeaderBits.Represents
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (tables hn ht ha hR outer) :=
  (controls hn ht ha hR outer).scalar.represents

noncomputable def leafSource (outer : Bool) :=if outer then IntegralFramedPhysicalLeafSources.outer hn ht ha R
  else IntegralFramedPhysicalLeafSources.marked hn ht ha R
noncomputable def originalSource (outer : Bool) :=if outer then IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R
  else IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R

def leafCount (n : List Bool→ℕ) (outer : Bool) (c : List Bool) :=number n (pairFst c)+(if outer then 10 else 8)
include hn in
theorem leafCount_unary (outer : Bool) : UnaryFn (leafCount n outer) :=by
  cases outer
  · exact IntegralFramedPhysicalLeafSources.markedCount_unary hn
  · exact IntegralFramedPhysicalLeafSources.outerCount_unary hn

include hR in
theorem leafSource_access (outer : Bool) : IntegerPolynomialRootQueriesBits.Access (leafSource hn ht ha (R:=R) outer) :=by
  cases outer
  · exact IntegralFramedPhysicalLeafSources.marked_access hn ht ha R hR
  · exact IntegralFramedPhysicalLeafSources.outer_access hn ht ha R hR

theorem source_packet (outer : Bool) (ctx : List Bool) (i : ℕ) :
    (leafSource hn ht ha (R:=R) outer).polynomial (pair (pair ctx []) (BinaryNatCode.encode i))=
      (originalSource hn ht ha (R:=R) outer).polynomial (pair ctx (BinaryNatCode.encode i)) :=by
  cases outer <;> exact IntegralFramedPhysicalLeafSources.source_packet _ ctx i

theorem key_root (outer : Bool) (ctx : List Bool) : pairFst ((bank hn ht ha hR outer).key (pair ctx []))=ctx :=by
  cases outer <;> simp only [bank,Bool.false_eq_true,ite_false,ite_true,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank,IntegralMixedAuxiliaryOuterRecordPlan.bank,
    IntegralMixedAuxiliaryMarkedRecordPlan.bankKey,IntegralMixedAuxiliaryOuterRecordPlan.bankKey,
    IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]

theorem count_bound (outer : Bool) (ctx : List Bool) : leafCount n outer (pair ctx [])≤
    (IntegralMixedFramedBankSnapshotBits.atKey (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data ((bank hn ht ha hR outer).key (pair ctx []))).count :=by
  cases outer
  · change _≤(IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR) (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (pair ctx []))).count
    rw [IntegralMixedAuxiliaryMarkedRecordPlan.bank_count]
    simp only [leafCount,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,pairFst_pair,Bool.false_eq_true,ite_false]
    omega
  · change _≤(IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedAuxiliaryOuterRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedPlan hn ht ha hR) (IntegralMixedAuxiliaryOuterRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.bankKey n (pair ctx []))).count
    rw [IntegralMixedAuxiliaryOuterRecordPlan.bank_count]
    simp only [leafCount,IntegralMixedAuxiliaryOuterRecordPlan.fullCount,pairFst_pair,ite_true]
    omega
end LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
