/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordCaller
public import LeanCanny.Encoding.IntegralFramedBankQuery
/-! # The actual completed causal replay bank has native univariate access -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem count_prefix (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (atKey P D H key).count=IntegralMixedFramedHistoryFamilyBits.prefixLength P key :=
  IntegralMixedFramedHistoryFamilyBits.family_birth P D H key
end LeanCanny.Algebra.IntegralMixedFramedBankSnapshotBits

namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def fullCount (n : List Bool→ℕ) (root : List Bool) := number n root+8+IntegralMixedCausalRecordPlanBits.count root

theorem fullCount_unary {n : List Bool→ℕ} (hn : UnaryFn n) : UnaryFn (fullCount n) :=
  ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8)).add IntegralMixedCausalRecordPlanBits.count_unary

def bankKey (n : List Bool→ℕ) (input : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst input) (fullCount n (pairFst input)) []

theorem bankKey_FP {n : List Bool→ℕ} (hn : UnaryFn n) : bankKey n∈FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (BinaryFn.ofUnary ((fullCount_unary hn).comp pairFst_mem_FP)).bits_mem_FP
    (constFn_mem_FP []))

theorem bank_count {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (input : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (certifiedData hn ht ha hR) (bankKey n input)).count=fullCount n (pairFst input) := by
  rw [IntegralMixedFramedBankSnapshotBits.count_prefix]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _
    (by change fullCount n (pairFst input)≤fullCount n (pairFst input)+2+1; omega)

def bankIndex (n : List Bool→ℕ) (input : List Bool) := Nat.fromBitsLE (pairSnd input)%fullCount n (pairFst input)

theorem bankIndex_unary {n : List Bool→ℕ} (hn : UnaryFn n) : UnaryFn (bankIndex n) := by
  have HC:UnaryFn (fun q=>fullCount n (pairFst q)) := (fullCount_unary hn).comp pairFst_mem_FP
  have HI:BinaryFn (bankIndex n) := (BinaryFn.fromBits pairSnd_mem_FP).mod (BinaryFn.ofUnary HC)
  refine (UnaryFn.fromBitsLE_min HI.bits_mem_FP HC).of_eq (fun q=>?_)
  rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (Nat.le_of_lt (Nat.mod_lt _ (by unfold fullCount; omega)))

noncomputable def bank {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : IntegralFramedBankQuery.Bank where
  parameters:=certifiedParameters hn ht ha hR
  plan:=certifiedPlan hn ht ha hR
  data:=certifiedData hn ht ha hR
  nodes _:=3
  factor:=factor hn ht ha
  seed:=IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR
  bounds:=certifiedInputs hn ht ha hR
  key:=bankKey n
  positive input:=by rw [bank_count]; unfold fullCount; omega
  coordinate input:=⟨bankIndex n input,by rw [bank_count]; exact Nat.mod_lt _ (by unfold fullCount; omega)⟩

noncomputable def bank_access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : IntegralFramedBankQuery.Access (bank hn ht ha hR) where
  parameters:=certifiedAccess hn ht ha hR
  liftedData:=callerData hn ht ha hR
  controls:=callerControls hn ht ha hR
  bounds:=callerBounds hn ht ha hR
  nodes:=BinaryFn.const 3
  factor:=factor_binary hn ht ha
  seed:=IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR
  key:=bankKey_FP hn
  coordinate:=bankIndex_unary hn

theorem bankIndex_packet (n : List Bool→ℕ) (root : List Bool) (i : ℕ) (hi : i<fullCount n root) :
    bankIndex n (pair root (BinaryNatCode.encode i))=i := by
  simp only [bankIndex,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact Nat.mod_eq_of_lt hi

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
