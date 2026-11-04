/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalRule
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalCaptures
public import LeanCanny.Geometry.IntegralMixedMatchedSlabNearEdge
/-! # A constructed matched branch gives genuine coordinate Near certificates -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open IntegralMixedOriginalRegularSource (radius radius_binary)
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
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>next d hk
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "rho"=>FrozenCoordinateOrdering.permutation (Frame.frozen (frame d hk))
local notation "CX"=>IntegralMixedCoordinateRename.state x rho
local notation "CR"=>cutRule x (Descriptor.frame d) h g hg
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "a"=>left.value V
local notation "b"=>right.value V

noncomputable local instance properAppendLocalNearIndexFintype :Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) oldCs):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedRoadmapProperParent.hom
  IntegralMixedRoadmapLocalFrame.field IntegralMixedPhysicalFieldEquality.point
  IntegralMixedRoadmapProperRow.parentKey IntegralMixedSelectedRootRank.rank
  IntegralMixedSelectedCoordinateEndpoint.Near

private theorem canonical_offset :(CR).critical.offset.val=IntegralMixedRoadmapAtomic.depth old+1:=by
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  exact (frozen_card d hk).trans (congrArg (·+1) HL)

private theorem canonical_objective :(CR).critical.objective=0:=by
  change ((rho).symm g).val-(frame d hk).frozen.card=0
  rw [(prefix_frozen d hk).permutation,frozen_card]
  have H:=IntegralMixedRoadmapProperParent.objective_value hn ht ha hR0 old hv hd
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  omega

/-- A single actual matched branch gives the entire genuine coordinate
certificate at every free original coordinate on W's own accepted packet. -/
theorem WordReceipt.coordinate_meaning_of_matched_branch
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (frame d hk) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical CX hm CR phi ((a+b)/2))
    {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u
      (M.curve fiber ((a+b)/2)∘(rho).symm) (M.curve fiber (if side then b else a)∘(rho).symm))
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    IntegralMixedRoadmapProperRow.CoordinateMeaning hn ht ha hR0 side
      (packet D old R.leftSpec R.rightSpec side W.word) j hV:=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  let z:=pair q (BinaryNatCode.encode j)
  let key:=IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z
  let fields:=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hV
  let pMID:=M.curve fiber ((a+b)/2)∘(rho).symm
  let pChild:=M.curve fiber (if side then b else a)∘(rho).symm
  have HD :0<IntegralMixedRoadmapAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  have HR:=IntegralMixedRoadmapProperRow.row_good_of_valid hn ht ha hR0 q hV HD j
    (by dsimp only [q];rw [depth_packet];exact hj) (by dsimp only [q];rw [dimension_packet];exact hjn)
  have HS :IntegralMixedRoadmapProperRowWitness.SideGood side z:=by
    simp only [IntegralMixedRoadmapProperRowWitness.SideGood,IntegralMixedRoadmapProperRow.atomic,z,
      pairFst_pair,IntegralMixedRoadmapProper.levelIndex,q,payload_packet,depth_packet,Nat.add_sub_cancel]
    unfold payload IntegralMixedRoadmapChain.sideWord IntegralMixedRoadmapAtomic.depth
    rw [IntegralMixedRoadmapChain.append_entry_last]
    cases side <;> simp only [IntegralMixedRoadmapChain.levelEntry,WordList.get_encode] <;> rfl
  obtain ⟨ψ,Hψ⟩:=IntegralMixedRoadmapProperRow.exists_original_interpretation hn ht ha hR0 q hV j
  let coord:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G key
    (get (BK).parameters Field.slot13 (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 false z))
  have HO:=canonical_offset hn ht ha hR0 old hv hd
  have HA:=row_ambient hn ht ha hR0 old hv hd left right R side W.word j
  have HDIM:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  let rel :Fin ((P).ambient c-(CR).critical.offset.val+1):=⟨j-(IntegralMixedRoadmapAtomic.depth old+1),by omega⟩
  have HRel :rel.val=coord.val:=by
    exact (row_coordinate hn ht ha hR0 old hv hd left right R side W.word hV j hj hjn).symm
  obtain ⟨ij,Hij,HMidField,HChildField⟩:=W.original_capture_fields hn ht ha hR0 old hv hd left right R side
    N hV j hj hjn
  let ix:=ClearedCoordinateCritical.freeIndex (CR).critical.offset.val (IntegralMixedCriticalSweep.fit CR).le rel
  have HI :ix=ij:=by
    apply Fin.ext
    change (CR).critical.offset.val+rel.val=ij.val
    exact (congrArg₂ Nat.add HO (show rel.val=j-(IntegralMixedRoadmapAtomic.depth old+1) from rfl)).trans
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
    exact (W.row_normalized hn ht ha hR0 old hv hd left right R side hV hOld j hj hjn ell
      (hell.trans_eq HO)).symm
  have HActualNear:IntegralMixedSelectedCoordinateEndpoint.Near ((G).state key) ((G).birth_bound key)
      ((G).rule key) ψ a b (if side then b else a) coord
      (IntegralMixedSelectedRootRank.rank ((G).state key) ((G).birth_bound key)
        ((G).rule key) ψ ((a+b)/2) coord (pMID ij)) (pChild ij):=by
    apply (source_near HA.symm (row_source hn ht ha hR0 old hv hd left right R side W.word j).symm
      CX hm ((G).state key) ((G).birth_bound key) CR ((G).rule key) rfl
      (row_current hn ht ha hR0 old hv hd left right R side W.word hV j hj hjn)
      (HO.trans (row_offset hn ht ha hR0 old hv hd left right R side W.word hV j hj hjn).symm)
      ((canonical_objective hn ht ha hR0 old hv hd).trans
        (row_objective hn ht ha hR0 old hv hd left right R side W.word hV j hj hjn).symm)
      phi ψ V (fun i :Fin ((G).birth key)=>fields ((G).birth key-1-i.val))
      (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) Hψ HN rel coord HRel
      a b (if side then b else a) ((a+b)/2) (pMID ij) (pChild ij)).mpr
    exact HNearValues
  have HE:=W.original_endpoint_fields hn ht ha hR0 old hv hd left right R side N hV
  have HSide :fields (IntegralMixedRoadmapProper.producer side q)=(if side then b else a):=by
    cases side
    · exact HE.1
    · exact HE.2
  dsimp only [fields,q] at HSide
  refine ⟨HR,HS,ψ,Hψ,?_⟩
  simpa only [HE.1,HE.2,HSide,HMidField,HChildField] using HActualNear

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
