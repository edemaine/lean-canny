/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerCutReceipt
public import LeanCanny.Encoding.IntegralMixedMarkedReservedRuling
/-! # The actual original marked plan binds the whole chosen cut selection -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedSelectionReceipt
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank IntegralMixedSourceIntegerRecordAppend.plan
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
variable (key : List Bool) (codes : List (List Bool)) (code labels : List Bool) (values : ℕ→ℝ) (a : ℝ)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (codes++[code]))
 (hk : prefixLength (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters key=number n (pairFst key)+8+codes.length)

include htable hk in
theorem native_root
    (hcoded : (IntegralMixedPrefixSnapshot.ofState ((family P (B).plan (B).data).state key)).CodedFactor labels values a code) :
    (IntegralMixedCutCreationReceipt.native P (B).plan (B).data key).HasRoot values a:=by
 have HP:=IntegralMixedSourceIntegerCutReceipt.native_root P
   (fun root _=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
   (fun root _=>IntegralMixedMarkedReservedCutView.degree hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
   (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0) (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) key codes code labels values a htable hk
 have HE:=congrArg (fun dh : (D : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P D=>
   (IntegralMixedPrefixSnapshot.ofState ((family P dh.1 dh.2).state key)).CodedFactor labels values a code→
     (IntegralMixedCutCreationReceipt.native P dh.1 dh.2 key).HasRoot values a)
   (IntegralMixedMarkedReservedRuling.planData_eq hn ht ha hR0)
 exact (HE.mp HP) hcoded

include htable hk in
theorem native_receipt
    (hcoded : (IntegralMixedPrefixSnapshot.ofState ((family P (B).plan (B).data).state key)).CodedFactor labels values a code) :
    IntegralMixedCutCreationReceipt.atKey P (B).plan (B).data key=some (IntegralMixedCutCreationReceipt.native P (B).plan (B).data key) ∧
      (IntegralMixedCutCreationReceipt.native P (B).plan (B).data key).HasRoot values a:=by
 have HP:=IntegralMixedSourceIntegerCutReceipt.native_receipt P
   (fun root _=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
   (fun root _=>IntegralMixedMarkedReservedCutView.degree hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
   (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0) (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) key codes code labels values a htable hk
 have HE:=congrArg (fun dh : (D : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P D=>
   (IntegralMixedPrefixSnapshot.ofState ((family P dh.1 dh.2).state key)).CodedFactor labels values a code→
     IntegralMixedCutCreationReceipt.atKey P dh.1 dh.2 key=some (IntegralMixedCutCreationReceipt.native P dh.1 dh.2 key) ∧
       (IntegralMixedCutCreationReceipt.native P dh.1 dh.2 key).HasRoot values a)
   (IntegralMixedMarkedReservedRuling.planData_eq hn ht ha hR0)
 exact (HE.mp HP) hcoded

end LeanCanny.Encoding.IntegralMixedMarkedReservedSelectionReceipt
