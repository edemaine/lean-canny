/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCoordinateData
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendLocalCaptures
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateMeaningComplete
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderLocalEdge
public import LeanCanny.Geometry.IntegralMixedMatchedSlabNearEdge
public import LeanCanny.Geometry.IntegralMixedNumericalSweepNear
/-! # A constructed matched branch gives genuine coordinate Near certificates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem source_near {a b S B m T C l :ℕ} {P :SpatialSource a} {Q :SpatialSource b} {ι κ :Type}
    (hab :a=b) (hP :HEq P Q) (x :State P S B m ι) (hm :m≤S) (y :State Q T C l κ) (hl :l≤T)
    (r :Rule a) (s :Rule b) (hr :r.slope=commonDenominator x) (hs :s.slope=commonDenominator y)
    (hoff :r.critical.offset.val=s.critical.offset.val) (hobj :r.critical.objective=s.critical.objective)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ :y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values :Fin m→ℝ) (other :Fin l→ℝ)
    (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K :∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN :∀i,i<r.critical.offset.val→IntegralMixedNumericalSweep.normalized r values i=
      IntegralMixedNumericalSweep.normalized s other i)
    (j :Fin (a-r.critical.offset.val+1)) (k :Fin (b-s.critical.offset.val+1)) (hjk :j.val=k.val)
    (lo hi endpoint t mid child :ℝ):
    IntegralMixedSelectedCoordinateEndpoint.Near y hl s ψ lo hi endpoint k
      (IntegralMixedSelectedRootRank.rank y hl s ψ t k mid) child↔
    IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ lo hi endpoint j
      (IntegralMixedSelectedRootRank.rank x hm r φ t j mid) child:=by
  subst b
  have HQ :P=Q:=eq_of_heq hP
  subst Q
  have HO :r.critical.offset=s.critical.offset:=Fin.ext hoff
  have HE :IntegralMixedNumericalSweep.indexCast r s HO j=k:=Fin.ext hjk
  rw [←HE]
  exact IntegralMixedNumericalSweep.anchored_near_iff_of_levels x hm y hl r s hr hs HO hobj φ ψ values other H K HN _ _ _ _ _ _ j

private theorem matched_near {a S B m :ℕ} {P :SpatialSource a} {ι :Type}
    (x :State P S B m ι) (hm :m≤S) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F :Frame a) (h :Fin (a+1)) (hh :h∈F.frozen) (g :Fin (a+1)) (hg :g∉F.frozen)
    (values :Fin m→ℝ) (lo hi :ℝ) (center :Set.Ioo lo hi)
    (M :MatchedSlabInterior x hm φ F h hh g hg values lo hi center)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ center.val)
    (endpoint :ℝ) (he :endpoint∈Set.Icc lo hi)
    (j :IntegralMixedSelectedGeometry.Free (sweep x F h hh g hg)):
    IntegralMixedSelectedCoordinateEndpoint.Near
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ lo hi endpoint j
      (IntegralMixedSelectedRootRank.rank
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
        (sweep x F h hh g hg) φ center.val j
        (M.curve fiber center.val (ClearedCoordinateCritical.freeIndex
          (sweep x F h hh g hg).critical.offset.val (IntegralMixedCriticalSweep.fit _).le j)))
      (M.curve fiber endpoint (ClearedCoordinateCritical.freeIndex
        (sweep x F h hh g hg).critical.offset.val (IntegralMixedCriticalSweep.fit _).le j)):=by
  have HN:=((M.near fiber endpoint he (M.curve fiber endpoint) (M.physical fiber endpoint he).1).mpr rfl) j
  rw [M.code_anchor fiber] at HN
  have HD:=IntegralMixedFrozenFrameSectionCode.word_digit
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ center.val fiber j
  change IntegralMixedSelectedCoordinateEndpoint.Near _ _ _ _ _ _ _ _
    (Nat.fromBitsLE (((IntegralMixedFrozenFrameSectionCode.word _ _ _ _ _ fiber).drop (j.val*B)).take B)) _ at HN
  rw [HD,IntegralMixedSelectedRootRank.ordinal_rank] at HN
  rw [M.anchor fiber]
  exact HN

private theorem canonical_rule_offset {a S B m :ℕ} {P :SpatialSource a} {ι :Type}
    (x :State P S B m ι) (d :Descriptor a m) (hk :d.labels.length<a+1)
    (g :Fin (a+1)) (hg :g∉(frame d hk).frozen) :
    (cutRule x d.frame (next d hk) g hg).critical.offset.val=d.labels.length+1 := by
  change (frame d hk).frozen.card=_
  exact frozen_card d hk

variable (old :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd :FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "e"=>FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c"=>FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension old
local notation "oldCs"=>FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x"=>FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "d"=>FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he
local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "V"=>FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd e he
local notation "phi"=>FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd e he
local notation "g"=>FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg"=>FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
local notation "h"=>next d hk
local notation "hm"=>FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd e he
local notation "rho"=>FrozenCoordinateOrdering.permutation (Frame.frozen (frame d hk))
local notation "CX"=>IntegralMixedCoordinateRename.state x rho
local notation "CR"=>cutRule x (Descriptor.frame d) h g hg
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
variable (left right :ParentEndpoint old hv hd)
  (R :CanonicalPair old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot old R.leftSpec R.rightSpec side
local notation "a"=>left.value V
local notation "b"=>right.value V

noncomputable local instance providerProperAppendCoordinatesIndexFintype :Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) oldCs):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) oldCs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderProperRow.parentKey IntegralMixedSelectedRootRank.rank
  IntegralMixedSelectedCoordinateEndpoint.Near

private theorem coordinate_plain_depth_eq (q :List Bool) :IntegralMixedRoadmapAtomic.depth q=
    FormulaSignSlotRadialProviderAtomic.depth q:=by
  unfold IntegralMixedRoadmapAtomic.depth FormulaSignSlotRadialProviderAtomic.depth
    IntegralMixedRoadmapAtomic.payload FormulaSignSlotRadialProviderAtomic.payload
  rfl

private theorem canonical_offset :(CR).critical.offset.val=FormulaSignSlotRadialProviderAtomic.depth old+1:=by
  have HL:=FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he
  exact (canonical_rule_offset x d hk g hg).trans (congrArg (·+1) HL)

private theorem canonical_objective :(CR).critical.objective=0:=by
  change ((rho).symm g).val-(frame d hk).frozen.card=0
  rw [(prefix_frozen d hk).permutation,frozen_card]
  have H : (g).val=(d).labels.length+1:=rfl
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  omega

/-- A single actual matched branch gives the entire genuine coordinate
certificate at every free original coordinate on W's own accepted packet. -/
theorem SampledLevel.coordinate_meaning_of_matched_branch
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (frame d hk) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical CX hm CR phi ((a+b)/2))
    (S :SampledLevel old hv hd left right R side
      (M.curve fiber ((a+b)/2)∘(rho).symm) (M.curve fiber (if side then b else a)∘(rho).symm))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D):
    FormulaSignSlotRadialProviderProperRow.CoordinateMeaning side
      (packet D old R.leftSpec R.rightSpec side S.receipt.word) j S.atomic_valid:=by
  let q:=packet D old R.leftSpec R.rightSpec side S.receipt.word
  let z:=pair q (BinaryNatCode.encode j)
  let key:=FormulaSignSlotRadialProviderProperRow.parentKey false z
  let fields:=FormulaSignSlotRadialProviderAtomic.field q S.atomic_valid
  let pMID:=M.curve fiber ((a+b)/2)∘(rho).symm
  let pChild:=M.curve fiber (if side then b else a)∘(rho).symm
  have HD :0<FormulaSignSlotRadialProviderAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  have HR:=FormulaSignSlotRadialProviderProperRow.row_good_of_valid q S.atomic_valid HD j
    (by dsimp only [q];rw [depth_packet];exact hj) (by dsimp only [q];rw [dimension_packet];exact hjn)
  have HS :FormulaSignSlotRadialProviderProperRowWitness.SideGood side z:=by
    simp only [FormulaSignSlotRadialProviderProperRowWitness.SideGood,FormulaSignSlotRadialProviderProperRow.atomic,z,
      pairFst_pair,IntegralMixedRoadmapProper.levelIndex,coordinate_plain_depth_eq,q,payload_packet,depth_packet,Nat.add_sub_cancel]
    unfold payload IntegralMixedRoadmapChain.sideWord FormulaSignSlotRadialProviderAtomic.depth
    rw [IntegralMixedRoadmapChain.append_entry_last]
    cases side <;> simp only [IntegralMixedRoadmapChain.levelEntry,WordList.get_encode] <;> rfl
  obtain ⟨ψ,Hψ⟩:=FormulaSignSlotRadialProviderProperRow.exists_original_interpretation q S.atomic_valid j
  let coord:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G key
    (get (BK).parameters Field.slot13 (FormulaSignSlotRadialProviderProperRow.parent false z))
  have HO:=canonical_offset old hv hd
  have HA:=row_ambient old hv hd left right R side S.receipt.word j
  have HDIM:=FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
  let rel :Fin ((P).ambient c-(CR).critical.offset.val+1):=⟨j-(FormulaSignSlotRadialProviderAtomic.depth old+1),by omega⟩
  have HRel :rel.val=coord.val:=by
    exact (row_coordinate old hv hd left right R side S.receipt.word S.atomic_valid j hj hjn).symm
  obtain ⟨ij,Hij,HMidField,HChildField⟩:=S.original_capture_fields j hj hjn
  let ix:=ClearedCoordinateCritical.freeIndex (CR).critical.offset.val (IntegralMixedCriticalSweep.fit CR).le rel
  have HI :ix=ij:=by
    apply Fin.ext
    change (CR).critical.offset.val+rel.val=ij.val
    exact (congrArg₂ Nat.add HO (show rel.val=j-(FormulaSignSlotRadialProviderAtomic.depth old+1) from rfl)).trans
      ((Nat.add_sub_of_le hj).trans Hij.symm)
  have HP :rho=Equiv.refl _ :=(prefix_frozen d hk).permutation
  have HMidPoint :M.curve fiber ((a+b)/2) ix=pMID ij:=by
    simp only [pMID,Function.comp_apply,HP,Equiv.refl_symm,Equiv.refl_apply]
    exact congrArg (M.curve fiber ((a+b)/2)) HI
  have HChildPoint :M.curve fiber (if side then b else a) ix=pChild ij:=by
    simp only [pChild,Function.comp_apply,HP,Equiv.refl_symm,Equiv.refl_apply]
    exact congrArg (M.curve fiber (if side then b else a)) HI
  have HEndpoint :(if side then b else a)∈Set.Icc a b:=by
    cases side
    · simp only [Bool.false_eq_true,ite_false,Set.mem_Icc]
      exact ⟨le_rfl,hab.le⟩
    · simp only [ite_true,Set.mem_Icc]
      exact ⟨hab.le,le_rfl⟩
  have HNear:=matched_near x hm phi (frame d hk) h (Finset.mem_insert_self _ _) g hg V a b
    ⟨(a+b)/2,by constructor <;> linarith⟩ M fiber (if side then b else a) HEndpoint rel
  change IntegralMixedSelectedCoordinateEndpoint.Near CX hm CR phi a b (if side then b else a) rel
    (IntegralMixedSelectedRootRank.rank CX hm CR phi ((a+b)/2) rel (M.curve fiber ((a+b)/2) ix))
    (M.curve fiber (if side then b else a) ix) at HNear
  have HNearValues:=Eq.mp (congrArg₂
    (fun mid child :ℝ=>IntegralMixedSelectedCoordinateEndpoint.Near CX hm CR phi a b
      (if side then b else a) rel
      (IntegralMixedSelectedRootRank.rank CX hm CR phi ((a+b)/2) rel mid) child)
    HMidPoint HChildPoint) HNear
  have HN :∀ell,ell<(CR).critical.offset.val→IntegralMixedNumericalSweep.normalized CR V ell=
      IntegralMixedNumericalSweep.normalized ((G).rule key)
        (fun i :Fin ((G).birth key)=>fields ((G).birth key-1-i.val)) ell:=by
    intro ell hell
    exact (S.row_normalized old hv hd left right R side j hj hjn ell
      (hell.trans_eq HO)).symm
  have HActualNear:IntegralMixedSelectedCoordinateEndpoint.Near ((G).state key) ((G).birth_bound key)
      ((G).rule key) ψ a b (if side then b else a) coord
      (IntegralMixedSelectedRootRank.rank ((G).state key) ((G).birth_bound key)
        ((G).rule key) ψ ((a+b)/2) coord (pMID ij)) (pChild ij):=by
    apply (source_near HA.symm (row_source old hv hd left right R side S.receipt.word j).symm
      CX hm ((G).state key) ((G).birth_bound key) CR ((G).rule key) rfl
      (row_current old hv hd left right R side S.receipt.word S.atomic_valid j hj hjn)
      (HO.trans (row_offset old hv hd left right R side S.receipt.word S.atomic_valid j hj hjn).symm)
      ((canonical_objective old hv hd).trans
        (row_objective old hv hd left right R side S.receipt.word S.atomic_valid j hj hjn).symm)
      phi ψ V (fun i :Fin ((G).birth key)=>fields ((G).birth key-1-i.val))
      (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd e he) Hψ HN rel coord HRel
      a b (if side then b else a) ((a+b)/2) (pMID ij) (pChild ij)).mpr
    exact HNearValues
  have HE:=S.original_endpoint_fields
  have HSide :fields (IntegralMixedRoadmapProper.producer side q)=(if side then b else a):=by
    cases side
    · exact HE.1
    · exact HE.2
  dsimp only [fields,q] at HSide
  refine ⟨HR,HS,ψ,Hψ,?_⟩
  dsimp only [key,z,coord,pMID,pChild] at HActualNear
  with_unfolding_all
    simpa only [FormulaSignSlotRadialProviderProperRow.oldProducer,
    FormulaSignSlotRadialProviderProperRow.pointProducer,FormulaSignSlotRadialProviderProperRow.dimension,
    FormulaSignSlotRadialProviderProperRow.initial,FormulaSignSlotRadialProviderProperRow.atomic,
    FormulaSignSlotRadialProviderProperRow.coordinate,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,
      Nat.fromBitsLE_bits,Bool.false_eq_true,ite_false,ite_true,HE.1,HE.2,HSide,HMidField,HChildField] using HActualNear


theorem SampledLevel.coordinates_of_matched_branch
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (frame d hk) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical CX hm CR phi ((a+b)/2))
    (S :SampledLevel old hv hd left right R side
      (M.curve fiber ((a+b)/2)∘(rho).symm) (M.curve fiber (if side then b else a)∘(rho).symm))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D) :
    FormulaSignSlotRadialProviderProperCoordinateSearch.Holds side
      (pair (packet D old R.leftSpec R.rightSpec side S.receipt.word) (BinaryNatCode.encode j)) :=by
  apply FormulaSignSlotRadialProviderProperRow.holds_of_coordinate_meaning side _ j S.atomic_valid
    (by rw [depth_packet];omega)
  · have HE:=S.original_endpoint_fields
    rw [HE.1,HE.2]
    exact hab
  · exact S.coordinate_meaning_of_matched_branch old hv hd left right R side hab M fiber j hj hjn

variable {old hv hd left right R side}

theorem SampledLevel.all_coordinates_of_matched_branch
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (frame d hk) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical CX hm CR phi ((a+b)/2))
    (S :SampledLevel old hv hd left right R side
      (M.curve fiber ((a+b)/2)∘(rho).symm) (M.curve fiber (if side then b else a)∘(rho).symm)) :
    FormulaSignSlotRadialProviderLocalEdge.allCoordinates side
      (packet D old R.leftSpec R.rightSpec side S.receipt.word) :=by
  intro i hi
  have HC:=hi
  unfold FormulaSignSlotRadialProviderLocalEdge.count IntegralMixedRoadmapProper.captureCount
    IntegralMixedRoadmapProper.levelIndex at HC
  rw [coordinate_plain_depth_eq,dimension_packet,depth_packet] at HC
  have H:=S.coordinates_of_matched_branch old hv hd left right R side hab M fiber
    (FormulaSignSlotRadialProviderAtomic.depth old+1+i) (by omega) (by omega)
  simpa only [FormulaSignSlotRadialProviderLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,
    List.length_replicate,depth_packet] using H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
