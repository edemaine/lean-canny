/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicFrame
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
public import LeanCanny.Geometry.IntegralMixedAtomicOccurrence
/-! # Every accepted atomic vertex has one actual geometric atomic occurrence -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

noncomputable def ownBirth (q :List Bool):=endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1
theorem context_root (q :List Bool):pairFst ((B).key (context q))=root q:=by
  unfold context
  exact IntegralMixedPhysicalMarkedPlan.key_root hn ht ha (radius_binary hR0) false (root q)
theorem native_dimension (q :List Bool):(P).ambient (pairFst ((B).key (context q)))=dimension hn ht ha hR0 q:=by
  rw [context_root hn ht ha hR0 q]
  rfl

theorem own_active (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (context q) (ownBirth hn ht ha hR0 q):=by
  have HD:=depth_le hn ht ha hR0 q hv
  have HF :0<free (dimension hn ht ha hR0 q) q:=by unfold free;omega
  obtain ⟨HB,_,_⟩:=companions hn ht ha hR0 q hv (free (dimension hn ht ha hR0 q) q-1) (by omega)
  have HE:=latest_block_end hn ht ha hR0 q hv
  have HH :first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+
      (free (dimension hn ht ha hR0 q) q-1)=ownBirth hn ht ha hR0 q:=by unfold ownBirth;omega
  exact HH ▸ HB

theorem native_point_good (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key (context q))))
      (ownBirth hn ht ha hR0 q) (frozen q) (depth q) (depth q):=by
  rw [native_dimension hn ht ha hR0 q]
  exact own_point_good hn ht ha hR0 q hv

theorem native_creating_command (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (pairFst ((B).key (context q))) (ownBirth hn ht ha hR0 q)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key (context q))))
        (ownBirth hn ht ha hR0 q) (frozen q) (depth q) (depth q) (native_point_good hn ht ha hR0 q hv)).rule:=by
  exact IntegralMixedStaticRecordLookup.critical_root_transport P D (root q) _
    (context_root hn ht ha hR0 q).symm (ownBirth hn ht ha hR0 q) (frozen q) (depth q) (depth q)
    (own_point_good hn ht ha hR0 q hv) (native_point_good hn ht ha hR0 q hv)
    (own_creating_command hn ht ha hR0 q hv)

noncomputable def source (q :List Bool):=
  (IntegralMixedFramedRootPullback.instructionAt P D (pairFst ((B).key (context q))) (ownBirth hn ht ha hR0 q)).source

theorem source_original (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    HEq (source hn ht ha hR0 q) (IntegralMixedOriginalRegularSource.source n t R0 (original q)):=by
  have HK:=context_root hn ht ha hR0 q
  have HI:=IntegralMixedFramedRootPullback.instructionAt_congr P D _ _
    (ownBirth hn ht ha hR0 q) (ownBirth hn ht ha hR0 q) HK rfl
  have HS:=IntegralMixedFramedRootPullback.instruction_read_heq (fun _ _ I=>I.source) _ _
    (congrArg (P).ambient HK) (congrArg (P).width HK) HI
  have Hsource :HEq (IntegralMixedFramedRootPullback.instructionAt P D (root q) (ownBirth hn ht ha hR0 q)).source
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root q)):=by
    simpa only [ownBirth] using own_creating_source_heq hn ht ha hR0 q hv
  refine HS.trans (Hsource.trans ?_)
  rw [IntegralMixedOriginalRegularSource.spatial_source]
  exact IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ (by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      root,pairFst_pair,original])

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family source point dimension initial width sourceCap
  scalarBudget wordBudget root context payload candidate word ownBirth
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralFramedPhysicalSquare.point

noncomputable def levels (q :List Bool) (hv :Valid hn ht ha hR0 q) (i :ℕ):=
  IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    (context q) (word q) (full_valid hn ht ha hR0 q hv) (Nat.fromBitsLE (WordList.get (frozen q) i))

theorem occurrence (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedAtomicOccurrence.Occurrence (source hn ht ha hR0 q) (depth q) (levels hn ht ha hR0 q hv)
      (point hn ht ha hR0 q hv):=by
  unfold source
  have HG:=native_point_good hn ht ha hR0 q hv
  have HB:=own_active hn ht ha hR0 q hv
  have HC:=native_creating_command hn ht ha hR0 q hv
  have HR:=IntegralMixedPhysicalPointCompanionScan.frame_point hn ht ha (radius_binary hR0) false
    (context q) (word q) (full_valid hn ht ha hR0 q hv) (ownBirth hn ht ha hR0 q) HB
    (frozen q) (depth q) (depth q) HG HC
  have HP :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (context q) (word q) (full_valid hn ht ha hR0 q hv) (ownBirth hn ht ha hR0 q)=point hn ht ha hR0 q hv:=
    by simpa only [ownBirth] using own_height_point hn ht ha hR0 q hv
  rw [HP] at HR
  refine ⟨?_,HR.1,?_,?_⟩
  · rw [native_dimension hn ht ha hR0 q]
    exact depth_le hn ht ha hR0 q hv
  · intro i hi
    have HI :i.val<WordListRecords.count (frozen q):=by rw [frozen_count];exact hi
    have HE:=HR.2.1 i.val HI
    have HL:=HG.1.2 i.val HI
    have HB':=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false
      (context q) (ownBirth hn ht ha hR0 q) HB).1
    dsimp only at HB'
    exact HE.trans (IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0)
      (context q) (word q) (full_valid hn ht ha hR0 q hv) _ (by omega)).symm
  · intro i hi hig
    exact HR.2.2 i (by rw [frozen_count];exact hi) hig

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
