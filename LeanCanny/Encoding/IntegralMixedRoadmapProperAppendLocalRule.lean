/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalSweep
public import LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource
/-! # Actual coordinate rules share the genuine canonical projection data -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem renamed_source_refl {a :ℕ} (Q :SpatialSource a):
    IntegralMixedCoordinateRename.spatial Q (Equiv.refl _)=Q:=by
  cases Q
  simp only [IntegralMixedCoordinateRename.spatial,Equiv.refl_symm,Equiv.coe_refl,MvPolynomial.rename_id,AlgHom.id_apply]

private theorem raw_objective_zero (a m :ℕ) (labels :List Bool) (g j :ℕ)
    (H :IntegralMixedChronologicalCutCode.Good a m labels g j)
    (hg :g=WordListRecords.count labels+1) (Q :ℤ) (hQ :Q≠0):
    ((IntegralMixedChronologicalCutCode.rawData a m labels g j H).rule Q hQ).critical.objective=0:=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor a m labels H.1
  let hk:=IntegralMixedChronologicalCutCode.raw_fit a m labels g j H
  change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm ⟨g,H.2.2.1⟩).val-
    (frame d hk).frozen.card=0
  rw [(prefix_frozen d hk).permutation,frozen_card]
  have HL :d.labels.length=WordListRecords.count labels:=
    IntegralMixedChronologicalFrameCode.descriptor_length a m labels H.1
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  omega

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "packetW" w=>packet D old R.leftSpec R.rightSpec side w
local notation "keyW" w "," j=>IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false
  (pair (packetW w) (BinaryNatCode.encode j))
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapProperRow.parentKey IntegralMixedRoadmapProperRow.parentDimension
  IntegralMixedRoadmapProperRow.parentBirth IntegralMixedRoadmapProperRow.parentData

theorem row_source (w :List Bool) (j :ℕ):
    HEq ((G).spatial (keyW w, j))
      (IntegralMixedCoordinateRename.spatial Q (FrozenCoordinateOrdering.permutation (frame d hk).frozen)):=by
  have HI :IntegralMixedAuxiliaryMarkedIntegerSource.original (pairFst (keyW w, j))=
      IntegralMixedRoadmapAtomic.original old:=by
    rw [IntegralMixedRoadmapProperRow.parentKey_root]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      IntegralMixedRoadmapProperRow.root,IntegralMixedRoadmapProperRow.atomic,pairFst_pair,candidate_packet,
      IntegralMixedRoadmapAtomic.original]
  have HS:=IntegralMixedPhysicalOriginalSource.family_source hn ht ha hR0 false (keyW w, j)
  have HQ :HEq Q (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original old)):=by
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    apply IntegralMixedOriginalRegularSource.source_congr
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      IntegralMixedRoadmapRetainedAppend.preparedRoot,IntegralMixedRoadmapAtomic.root,
      IntegralMixedRoadmapRetainedAppend.candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]
  have HR :IntegralMixedCoordinateRename.spatial Q (FrozenCoordinateOrdering.permutation (frame d hk).frozen)=Q:=by
    rw [(prefix_frozen d hk).permutation]
    exact renamed_source_refl Q
  exact (HS.trans (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HI)).trans
    (HQ.symm.trans (heq_of_eq HR.symm))

theorem row_ambient (w :List Bool) (j :ℕ):
    (G).ambient (keyW w, j)=(P).ambient c:=by
  have H:=IntegralMixedRoadmapProperRow.parentDimension_eq hn ht ha hR0 false
    (pair (packetW w) (BinaryNatCode.encode j))
  have HE :(G).ambient (keyW w, j)=D:=by
    change (BK).parameters.ambient (pairFst (keyW w, j))=D
    simpa only [IntegralMixedRoadmapProperRow.parentDimension,IntegralMixedRoadmapProperRow.dimension,
      IntegralMixedRoadmapProperRow.atomic,pairFst_pair,dimension_packet] using H
  exact HE.trans (IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e).symm

private theorem row_good (w :List Bool)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packetW w))
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (pair (packetW w) (BinaryNatCode.encode j)):=by
  apply IntegralMixedRoadmapProperRow.row_good_of_valid hn ht ha hR0 _ hV
    (by rw [depth_packet];omega) j
  · rw [depth_packet]
    exact hj
  · rw [dimension_packet]
    exact hjn

theorem row_offset (w :List Bool)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packetW w))
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    ((G).rule (keyW w, j)).critical.offset.val=IntegralMixedRoadmapAtomic.depth old+1:=by
  have HA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapProperRow.atomic (pair (packetW w) (BinaryNatCode.encode j))):=by
    simpa only [IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hV
  have H:=IntegralMixedRoadmapProperRow.rule_offset hn ht ha hR0 false _ HA
    (row_good hn ht ha hR0 old hv hd left right R side w hV j hj hjn)
  have HE :IntegralMixedRoadmapProperRow.offset (pair (packetW w) (BinaryNatCode.encode j))=
      IntegralMixedRoadmapAtomic.depth old+1:=by
    simp only [IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.atomic,pairFst_pair,
      IntegralMixedRoadmapProper.levelIndex,depth_packet]
    omega
  exact H.trans HE

theorem row_objective (w :List Bool)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packetW w))
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    ((G).rule (keyW w, j)).critical.objective=0:=by
  let z:=pair (packetW w) (BinaryNatCode.encode j)
  have HA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z):=by
    simpa only [z,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hV
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z HA
  have HG:=row_good hn ht ha hR0 old hv hd left right R side w hV j hj hjn
  have HP:=IntegralMixedRoadmapProperRow.parent_good hn ht ha hR0 false z HC HG
  rw [IntegralMixedRoadmapProperRow.rule_at_parent hn ht ha hR0 false z HC HG]
  simp only [IntegralMixedRoadmapProperRow.parentData,Bool.false_eq_true,ite_false]
  have HRaw:=raw_objective_zero _ _ _ _ _ HP.1 (IntegralMixedRoadmapProperRow.offset_count z)
    (commonDenominator ((G).state (keyW w, j))) (commonDenominator_ne_zero ((G).state (keyW w, j)))
  unfold IntegralMixedRoadmapProperRow.parentDimension at HRaw ⊢
  exact HRaw

theorem row_current (w :List Bool)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packetW w))
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    ((G).rule (keyW w, j)).slope=commonDenominator ((G).state (keyW w, j)):=by
  let z:=pair (packetW w) (BinaryNatCode.encode j)
  have HA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z):=by
    simpa only [z,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hV
  exact IntegralMixedRoadmapProperRow.rule_current hn ht ha hR0 false z
    (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z HA)
    (row_good hn ht ha hR0 old hv hd left right R side w hV j hj hjn)

theorem row_coordinate (w :List Bool)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packetW w))
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (keyW w, j)
      (get (BK).parameters Field.slot13 (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 false
        (pair (packetW w) (BinaryNatCode.encode j))))).val=j-(IntegralMixedRoadmapAtomic.depth old+1):=by
  let z:=pair (packetW w) (BinaryNatCode.encode j)
  have HA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z):=by
    simpa only [z,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hV
  have H:=IntegralMixedRoadmapProperRow.selected_coordinate hn ht ha hR0 false z HA
    (row_good hn ht ha hR0 old hv hd left right R side w hV j hj hjn)
  have HE :IntegralMixedRoadmapProperRow.relativeCoordinate z=j-(IntegralMixedRoadmapAtomic.depth old+1):=by
    simp only [z,IntegralMixedRoadmapProperRow.relativeCoordinate,IntegralMixedRoadmapProperRow.coordinate,
      IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.atomic,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedRoadmapProper.levelIndex,depth_packet]
    omega
  exact H.trans HE

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
