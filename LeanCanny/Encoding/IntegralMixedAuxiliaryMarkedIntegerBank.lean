/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerCertified
public import LeanCanny.Encoding.IntegralFramedBankQuery
/-! # A native marked replay bank for joint-tuple univariate and Thom queries

Input pairs the complete marked context with a binary retained coordinate.
The entire n+8-birth prelude is selected; malformed indices are reduced modulo
that positive count. The native bank certificate has no evaluator field.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def bankKey (n : List Bool → ℕ) (input : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst input) (number n (pairFst input)+8) []

theorem bankKey_FP {n : List Bool → ℕ} (hn : UnaryFn n) : bankKey n∈FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (BinaryFn.ofUnary (((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).comp pairFst_mem_FP).add (UnaryFn.const 8))).bits_mem_FP
    (constFn_mem_FP []))

theorem bank_count {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) (input : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (certifiedData hn ht ha hR) (bankKey n input)).count=number n (pairFst input)+8 := by
  change (IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR)
    (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).birth (bankKey n input)=number n (pairFst input)+8
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ (by change _+8≤_+8+2+1; omega)

def bankIndex (n : List Bool → ℕ) (input : List Bool) := Nat.fromBitsLE (pairSnd input)%(number n (pairFst input)+8)

theorem bankIndex_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (bankIndex n) := by
  have HN : UnaryFn (fun q=>number n (pairFst q)+8) :=
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).comp pairFst_mem_FP).add (UnaryFn.const 8)
  have HI : BinaryFn (bankIndex n) := (BinaryFn.fromBits pairSnd_mem_FP).mod (BinaryFn.ofUnary HN)
  refine (UnaryFn.fromBitsLE_min HI.bits_mem_FP HN).of_eq (fun q=>?_)
  rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (Nat.le_of_lt (Nat.mod_lt _ (by omega : 0<number n (pairFst q)+8)))

noncomputable def bank {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) : IntegralFramedBankQuery.Bank where
  parameters:=certifiedParameters hn ht ha hR
  plan:=certifiedPlan hn ht ha hR
  data:=certifiedData hn ht ha hR
  nodes _:=1
  factor _:=1
  seed:=seed hn ht ha hR
  bounds:=certifiedInputs hn ht ha hR
  key:=bankKey n
  positive input:=by rw [bank_count]; omega
  coordinate input:=⟨bankIndex n input,by rw [bank_count]; exact Nat.mod_lt _ (by omega)⟩

noncomputable def bank_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) : IntegralFramedBankQuery.Access (bank hn ht ha hR) where
  parameters:=certifiedAccess hn ht ha hR
  liftedData:=certifiedCallerData hn ht ha hR
  controls:=certifiedCallerControls hn ht ha hR
  bounds:=certifiedCallerBounds hn ht ha hR
  nodes:=BinaryFn.const 1
  factor:=BinaryFn.const 1
  seed:=seed_binary hn ht ha hR
  key:=bankKey_FP hn
  coordinate:=bankIndex_unary hn

theorem bankIndex_packet (n : List Bool → ℕ) (context : List Bool) (i : ℕ) (hi : i<number n context+8) :
    bankIndex n (pair context (BinaryNatCode.encode i))=i := by
  simp only [bankIndex,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact Nat.mod_eq_of_lt hi

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
