/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicCapture
/-! # Every coordinate of an atomic signature reads the same physical point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family dimension initial width sourceCap
  scalarBudget wordBudget root context payload candidate word
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointCompanionScan.retained
  IntegralMixedPhysicalPointCompanionScan.selected

theorem signature_readback (q :List Bool) (hv :Valid hn ht ha hR0 q)
    (i :Fin ((P).ambient (pairFst ((B).key (context q)))+1)) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (context q) (word q) (full_valid hn ht ha hR0 q hv)
      (Nat.fromBitsLE (WordList.get (signature (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) i.val))=
      point hn ht ha hR0 q hv i :=by
  have HIn :i.val<dimension hn ht ha hR0 q+1:=by rw [←native_dimension hn ht ha hR0 q];exact i.isLt
  have HL:=IntegralMixedChronologicalPointSignatureCode.code_lookup (dimension hn ht ha hR0 q)
    (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (frozen q) ⟨i.val,HIn⟩
  change Nat.fromBitsLE (WordList.get (signature (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) i.val)=_ at HL
  rw [HL]
  by_cases hi :i.val<depth q
  · have HI :i.val<WordListRecords.count (frozen q):=by rw [frozen_count];exact hi
    rw [IntegralMixedChronologicalPointSignatureCode.producer,ite_eq_left HI]
    exact ((occurrence hn ht ha hR0 q hv).frozen i hi).symm
  · let j:=dimension hn ht ha hR0 q-i.val
    have HD:=depth_le hn ht ha hR0 q hv
    have HJ :j<free (dimension hn ht ha hR0 q) q:=by unfold j free;omega
    obtain ⟨HB,_,HR⟩:=companions hn ht ha hR0 q hv j HJ
    have HV:=IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
      (context q) (word q) (full_valid hn ht ha hR0 q hv)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j) HB
    have HS :IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (context q)
        (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j)=i.val:=by
      rw [capture_selected hn ht ha hR0 q hv j HJ]
      unfold j
      omega
    have HE :IntegralMixedChronologicalPointSignatureCode.producer (dimension hn ht ha hR0 q)
        (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (frozen q) i.val=
        first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j:=by
      unfold IntegralMixedChronologicalPointSignatureCode.producer
      rw [frozen_count,ite_eq_right hi]
      unfold j
      omega
    rw [HE]
    have HF :(⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (context q)
        (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j),
        IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ HB⟩:
        Fin ((P).ambient (pairFst ((B).key (context q)))+1))=i:=Fin.ext HS
    rw [HF] at HR
    exact HV.symm.trans HR

theorem signature_bounded (q :List Bool) (hv :Valid hn ht ha hR0 q)
    (i :Fin ((P).ambient (pairFst ((B).key (context q)))+1)) :
    Nat.fromBitsLE (WordList.get (signature (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) i.val)<
      IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context q):=by
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context q)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (context q)):=
    IntegralMixedFramedHistoryFamilyBits.family_birth P (B).plan (B).data ((B).key (context q))
  rw [HC]
  have HIn :i.val<dimension hn ht ha hR0 q+1:=by rw [←native_dimension hn ht ha hR0 q];exact i.isLt
  have HL:=IntegralMixedChronologicalPointSignatureCode.code_lookup (dimension hn ht ha hR0 q)
    (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (frozen q) ⟨i.val,HIn⟩
  change Nat.fromBitsLE (WordList.get (signature (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) i.val)=_ at HL
  rw [HL]
  change IntegralMixedChronologicalPointSignatureCode.producer (dimension hn ht ha hR0 q)
    (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (frozen q) i.val<
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (context q))
  unfold IntegralMixedChronologicalPointSignatureCode.producer
  rw [frozen_count]
  split_ifs with hi
  · have HH:=(own_frame_good hn ht ha hR0 q hv).2 i.val (by rw [frozen_count];exact hi)
    have HB:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false
      (context q) (ownBirth hn ht ha hR0 q) (own_active hn ht ha hR0 q hv)).1
    exact HH.trans HB
  · let j:=dimension hn ht ha hR0 q-i.val
    have HD:=depth_le hn ht ha hR0 q hv
    have HJ :j<free (dimension hn ht ha hR0 q) q:=by unfold j free;omega
    obtain ⟨HB,_,_⟩:=companions hn ht ha hR0 q hv j HJ
    have HT:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false
      (context q) (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j) HB).1
    dsimp only at HT
    have HE :first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+
        (dimension hn ht ha hR0 q+1-depth q)-1-(i.val-depth q)=
        first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j:=by unfold j;omega
    rw [HE]
    exact HT

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
