/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalPreparedParent
/-! # Construct native no-critical witnesses from the original frozen slice -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedPhysicalCriticalPrefixes (key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem critical_values_congr {a b m k : ℕ} (P : SpatialSource a) (Q : SpatialSource b)
    (hn : a=b) (hm : m=k) (hs : HEq P Q) (labels : List Bool)
    (ha : IntegralMixedChronologicalFrameCode.Good a m labels)
    (hb : IntegralMixedChronologicalFrameCode.Good b k labels)
    (h : Fin (a+1)) (g : Fin (b+1)) (hg : h.val=g.val)
    (v : Fin m→ℝ) (w : Fin k→ℝ) (hv : ∀(i : Fin m) (j : Fin k),i.val=j.val→v i=w j) :
    realCriticalValues P (line (IntegralMixedChronologicalFrameCode.descriptor a m labels ha).frame h) v h=
      realCriticalValues Q (line (IntegralMixedChronologicalFrameCode.descriptor b k labels hb).frame g) w g :=by
  cases hn
  cases hm
  have HP : P=Q:=eq_of_heq hs
  subst Q
  have HH : h=g:=Fin.ext hg
  subst g
  have HV : v=w:=funext (fun i=>hv i i rfl)
  subst w
  rfl

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "K"=>key n false false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

noncomputable local instance parentFintype (q : List Bool) : Fintype ((G).physical (K q)):=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0)
    (IntegralMixedFramedHistoryFamilyBits.commands P D (K q))))

private theorem full_word_at_critical (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (frame : Frame ((P).ambient (pairFst (K q))))
    (HA : AtomicRows frame ((G).birth (K q))) (HP : PrefixFrozen frame) (HF : FreeNormal frame)
    (h : Fin ((P).ambient (pairFst (K q))+1)) (hh : h∉frame.frozen)
    (hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D (K q)).command=
      .critical (HA.pointData h h hh hh).rule)
    (hn0 : 0<(G).ambient (K q)) (charge : ℕ)
    (hd : ((G).spatial (K q)).degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient (K q)+1)
      ((G).spatial (K q)).degree≤2^(G).width (K q)) (u : ℝ)
    (hu : u∈realCriticalValues ((G).spatial (K q)) (line frame h)
      (IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false q hp) h) :
    ∃w,∃_hv : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false true) q w,
      IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (radius_binary hR0) false (pair q w) :=by
  let : Fintype ((G).physical (K q)):=parentFintype hn ht ha hR0 q
  have HInterpretation:=IntegralFramedPhysicalSquare.exists_interpretation P D H L F C hs K
    (positive hn ht ha (radius_binary hR0) false false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp
  obtain ⟨φ,Hφ,Hvalues⟩:=HInterpretation
  have HV (i : Fin ((G).birth (K q))) :
      φ (((G).state (K q)).bank.numerator i)/(((G).state (K q)).bank.denominator i:ℝ)=
        IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false q hp i :=
    (Hvalues i).trans (IntegralFramedPhysicalSquare.bank_naturalPoint P D H L F C hs K
      (positive hn ht ha (radius_binary hR0) false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i).symm
  have HR:= (realCriticalWitness_iff ((G).state (K q))
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (K q)) ((G).birth_bound _)
    hn0 charge hd hcap frame HA HP HF h hh
    (IntegralFramedPhysicalSquare.rawPoint P D H L F C hs K
      (positive hn ht ha (radius_binary hR0) false false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
    (IntegralFramedPhysicalSquare.raw_roots P D H L F C hs K
      (positive hn ht ha (radius_binary hR0) false false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
    φ (by simpa only [IntegralFramedPhysicalSquare.rawPoint,Function.comp_apply] using Hφ)
    (IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false q hp) HV u).mpr hu
  have HN:= (IntegralMixedPhysicalCriticalInterval.naturalWitness_iff_actual hn ht ha (radius_binary hR0) false q
    frame HA h hh (IntegralMixedPhysicalCriticalInterval.parentArray hn ht ha (radius_binary hR0) false q hp)
    u hc φ HV).mpr HR
  obtain ⟨z,hz,hm,_,_⟩:=HN
  obtain ⟨w,hv,HZ⟩:=IntegralFramedPhysicalSquare.exists_joint_natural P D H L F C hs (key n false true)
    (positive hn ht ha (radius_binary hR0) false true) q z hz
  refine ⟨w,hv,?_⟩
  apply (IntegralMixedPhysicalCriticalInterval.agrees_iff_observations hn ht ha (radius_binary hR0) false
    q w hp hv z HZ).mpr
  intro i hi
  let j : Fin ((G).birth (K q)):=⟨i,by
    rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha (radius_binary hR0) false false]
    exact hi⟩
  have HE:=IntegralMixedPhysicalCriticalObservation.retained_observation P D H (K q)
    (HA.pointData h h hh hh).rule z q
    (IntegralMixedPhysicalCriticalInterval.parent_room hn ht ha (radius_binary hR0) false q) hc j
  rw [←IntegralMixedPhysicalCriticalInterval.child_key hn ht ha (radius_binary hR0) false q] at HE
  exact (IntegralMixedPhysicalCriticalInterval.bank_point_observation hn ht ha (radius_binary hR0) false false q _ hp _
    (IntegralMixedPhysicalCriticalInterval.parentArray_joint hn ht ha (radius_binary hR0) false q hp) i hi).trans
      ((hm j).trans HE.symm)

private noncomputable def parentCriticalValues (q w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false)
      (query hn ht ha hR0 (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q w)))) : Set ℝ:=
  let z:=query hn ht ha hR0 (pair q w)
  let HG:=parent_point_good hn ht ha hR0 q w hv hd
  realCriticalValues ((G).spatial (K z))
    (line (IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1).frame
      ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)
    (IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false z hp)
    ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩

private theorem parent_critical_values_original (q w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false)
      (query hn ht ha hR0 (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q w))))
    (Hvalues : ∀i : Fin ((G).birth (K (query hn ht ha hR0 (pair q w)))),
      IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false
        (query hn ht ha hR0 (pair q w)) hp i=originalNaturalValues hn ht ha hR0 q hv i.val) :
    parentCriticalValues hn ht ha hR0 q w hv hd hp=originalCriticalValues hn ht ha hR0 q hv hd :=by
  have HD : (G).ambient (K (query hn ht ha hR0 (pair q w)))=n (IntegralMixedRoadmapAtomic.original q)+3:=
    (query_key_dimension hn ht ha hR0 q w).trans (IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 q)
  have HM:=actual_parent_birth hn ht ha hR0 q w hv
  have HO : IntegralMixedAuxiliaryMarkedIntegerSource.original (pairFst (K (query hn ht ha hR0 (pair q w))))=
      IntegralMixedRoadmapAtomic.original q:=by
    simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair,
      IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      query_candidate,IntegralMixedRoadmapAtomic.original]
  have HS:= (IntegralMixedPhysicalOriginalSource.family_source hn ht ha hR0 false
    (K (query hn ht ha hR0 (pair q w)))).trans
      (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO)
  unfold parentCriticalValues originalCriticalValues originalDescriptor originalHeight
  apply critical_values_congr _ _ HD HM HS (IntegralMixedRoadmapProper.labels q)
    (parent_point_good hn ht ha hR0 q w hv hd).1 (original_point_good hn ht ha hR0 q hv hd).1 _ _ rfl
  intro i j hij
  exact (Hvalues i).trans (congrArg (originalField hn ht ha hR0 q hv)
    (congrArg (fun v : ℕ=>originalBirth hn ht ha hR0 q-1-v) hij))

private theorem producer_before_parent (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (side : Bool) : IntegralMixedRoadmapProper.producer side q<originalBirth hn ht ha hR0 q :=by
  have HG:=IntegralMixedRoadmapProper.midpoint_good hn ht ha hR0 q hv hd
  have HF:=IntegralMixedRoadmapProper.midpoint_fit hn ht ha hR0 q hv hd
  have HC : IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)):=by
    simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.packet,IntegralMixedRoadmapBadProbePacket.raw,pairFst_pair,pairSnd_pair]
  have HB : IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q+
        IntegralMixedRoadmapProper.midRawIndex (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q:=by
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HM : IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q≤originalBirth hn ht ha hR0 q:=by
    unfold originalBirth
    rw [HB,HC]
    omega
  cases side
  · exact HG.2.1.trans_le HM
  · exact HG.2.2.1.trans_le HM

private theorem query_guard (q w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedPhysicalCriticalInterval.Guard n false (query hn ht ha hR0 (pair q w)) :=by
  refine ⟨critical_query hn ht ha hR0 q w,?_,?_⟩
  · have HE:=query_endpoint hn ht ha hR0 false q w
    simp only [Bool.false_eq_true,ite_false] at HE
    rw [HE,query_birth hn ht ha hR0 q w (count_positive hn ht ha hR0 q hv)]
    exact producer_before_parent hn ht ha hR0 q hv hd false
  · have HE:=query_endpoint hn ht ha hR0 true q w
    simp only [ite_true] at HE
    rw [HE,query_birth hn ht ha hR0 q w (count_positive hn ht ha hR0 q hv)]
    exact producer_before_parent hn ht ha hR0 q hv hd true

private theorem endpoint_original (q w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false)
      (query hn ht ha hR0 (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q w))))
    (Hvalues : ∀i : Fin ((G).birth (K (query hn ht ha hR0 (pair q w)))),
      IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false
        (query hn ht ha hR0 (pair q w)) hp i=originalNaturalValues hn ht ha hR0 q hv i.val)
    (side : Bool) :
    IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha (radius_binary hR0) false
      (query hn ht ha hR0 (pair q w)) hp
      (Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (query hn ht ha hR0 (pair q w))
        else IntegralMixedPhysicalCriticalQuery.leftWord (query hn ht ha hR0 (pair q w))))=
      originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer side q) :=by
  rw [query_endpoint]
  have HB : IntegralMixedPhysicalCriticalPrefixes.birth n false false (query hn ht ha hR0 (pair q w))=
      originalBirth hn ht ha hR0 q:=query_birth hn ht ha hR0 q w (count_positive hn ht ha hR0 q hv)
  have HP:=producer_before_parent hn ht ha hR0 q hv hd side
  let i : Fin ((G).birth (K (query hn ht ha hR0 (pair q w)))):=
    ⟨IntegralMixedPhysicalCriticalPrefixes.birth n false false (query hn ht ha hR0 (pair q w))-1-
      IntegralMixedRoadmapProper.producer side q,by
      rw [actual_parent_birth hn ht ha hR0 q w hv,HB]
      omega⟩
  have HE : IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha (radius_binary hR0) false
      (query hn ht ha hR0 (pair q w)) hp (IntegralMixedRoadmapProper.producer side q)=
      IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false
        (query hn ht ha hR0 (pair q w)) hp i:=
    (IntegralMixedPhysicalCriticalContext.parentValues_point hn ht ha (radius_binary hR0) _ hp i).symm
  have HR : originalBirth hn ht ha hR0 q-1-i.val=IntegralMixedRoadmapProper.producer side q:=by
    dsimp only [i]
    rw [HB]
    omega
  exact HE.trans ((Hvalues i).trans (congrArg (originalField hn ht ha hR0 q hv) HR))

private theorem old_field_count (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q)=
      originalBirth hn ht ha hR0 q+1 :=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [IntegralMixedRoadmapAtomic.context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  have HN : IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q:=by
    rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,
      IntegralMixedRoadmapAtomic.original]
  have HC : IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q)=
      IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q):=by
    simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  have HP:=count_positive hn ht ha hR0 q hv
  unfold originalBirth
  rw [HN,HC]
  omega

private theorem new_field_count (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context hn ht ha hR0 q)=
      originalBirth hn ht ha hR0 q+1 :=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [context,pairFst_pair]
  have HF:=IntegralMixedPhysicalCriticalContext.full_birth (n:=n) (canonical hn ht ha hR0 q)
  have HS:=IntegralMixedPhysicalCriticalPrefixes.consecutive n false (canonical hn ht ha hR0 q)
  have HP:=query_birth hn ht ha hR0 q [] (count_positive hn ht ha hR0 q hv)
  change IntegralMixedPhysicalCriticalPrefixes.birth n false true (canonical hn ht ha hR0 q)=
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (root hn ht ha hR0 q) at HF
  rw [←HF,HS]
  simpa only [canonical,originalBirth] using congrArg (fun k : ℕ=>k+1) HP

private theorem field_context_congr (c d w : List Bool) (he : c=d)
    (hc : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) c w)
    (hd : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) d w)
    (i : ℕ) : IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) c w hc i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) d w hd i :=by
  subst d
  rfl

private theorem interval_transport {a b c d u : ℝ} (ha : a=c) (hb : b=d)
    (hu : u∈Ioo a b) : u∈Ioo c d :=by
  cases ha
  cases hb
  exact hu

attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
 IntegralMixedRoadmapProper.labels originalField originalNaturalValues originalCriticalValues parentCriticalValues

private theorem noCritical_from_parent (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (HF : OriginalSliceCriticalFree hn ht ha hR0 q hv hd) (wP : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false)
      (query hn ht ha hR0 (pair q wP))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q wP))))
    (hlen : wP.length=parentWidth hn ht ha hR0 q)
    (Hvalues : ∀i : Fin ((G).birth (K (query hn ht ha hR0 (pair q wP)))),
      IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false
        (query hn ht ha hR0 (pair q wP)) hp i=originalNaturalValues hn ht ha hR0 q hv i.val) :
    NoCritical hn ht ha hR0 q :=by
  let z:=query hn ht ha hR0 (pair q wP)
  let HG:=parent_point_good hn ht ha hR0 q wP hv hd
  let d:=IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1
  let h : Fin ((P).ambient (pairFst (K z))+1):=⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩
  have HH : h∉d.frame.frozen:=by
    rw [d.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapProper.labels_count]
    exact Nat.lt_irrefl _
  have HC : (IntegralMixedFramedHistoryFamilyBits.instruction P D (K z)).command=
      .critical (d.atomic.pointData h h HH HH).rule:=
    IntegralMixedPhysicalChronologicalCritical.command_key hn ht ha (radius_binary hR0) false z (prefixRoot q) wP
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q) HG
      (query_packet_key hn ht ha hR0 q wP)
  have HSet:=parent_critical_values_original hn ht ha hR0 q wP hv hd hp Hvalues
  obtain ⟨u,HU⟩:=original_critical_nonempty hn ht ha hR0 q hv hd
  have HU' : u∈realCriticalValues ((G).spatial (K z)) (line d.frame h)
      (IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false z hp) h:=by
    have HE:=(congrArg (fun s : Set ℝ=>u∈s) HSet).mpr HU
    unfold parentCriticalValues at HE
    exact HE
  have HFull:=full_word_at_critical hn ht ha hR0 z hp d.frame d.atomic d.prefix_frozen d.free_normal h HH HC
    (query_positive hn ht ha hR0 q wP) (t (IntegralMixedRoadmapAtomic.original q)).toData.size
    (query_degree hn ht ha hR0 q wP) ((G).scalar_cap (K z)) u HU'
  obtain ⟨wF,hvF,HAgree⟩:=HFull
  have hCrit : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedPhysicalCriticalContext.context z) wF:=
    (IntegralMixedPhysicalCriticalContext.valid_full hn ht ha (radius_binary hR0) z wF).mp hvF
  have hF : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (context hn ht ha hR0 q) wF:=by
    rw [←query_context hn ht ha hR0 q wP]
    exact hCrit
  have HBirth : IntegralMixedPhysicalCriticalPrefixes.birth n false false z=originalBirth hn ht ha hR0 q:=
    query_birth hn ht ha hR0 q wP (count_positive hn ht ha hR0 q hv)
  have HFields : ∀i<originalBirth hn ht ha hR0 q,
      originalField hn ht ha hR0 q hv i=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (context hn ht ha hR0 q) wF hF i:=by
    intro i hi
    let j : Fin ((G).birth (K z)):=⟨originalBirth hn ht ha hR0 q-1-i,by
      rw [actual_parent_birth hn ht ha hR0 q wP hv]
      omega⟩
    have HJ : originalBirth hn ht ha hR0 q-1-j.val=i:=by dsimp only [j];omega
    have HP:=Hvalues j
    have HE:=IntegralMixedPhysicalCriticalContext.parentValues_field hn ht ha (radius_binary hR0) z wF hp hvF hCrit HAgree j
    have HI : IntegralMixedPhysicalCriticalPrefixes.birth n false false z-1-j.val=i:=by rw [HBirth];exact HJ
    rw [HI] at HE
    have HV : originalNaturalValues hn ht ha hR0 q hv j.val=originalField hn ht ha hR0 q hv i:=by
      unfold originalNaturalValues
      exact congrArg (originalField hn ht ha hR0 q hv) HJ
    exact (HV.symm.trans (HP.symm.trans HE)).trans
      (field_context_congr hn ht ha hR0 _ _ wF (query_context hn ht ha hR0 q wP) hCrit hF i)

  let table:=IntegralMixedRoadmapBadProbePacket.matchTable (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
    (IntegralMixedRoadmapProper.badPacket q)
  have HTable : WordListRecords.count table=originalBirth hn ht ha hR0 q:=by
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_count]
    rfl
  have HB : ∀i<WordListRecords.count table,
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get table i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q) ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get table i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context hn ht ha hR0 q):=by
    intro i hi
    have HM : i<originalBirth hn ht ha hR0 q:=hi.trans_eq HTable
    have HL:=IntegralMixedRoadmapBadProbePacket.matchTable_lookup
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapProper.badPacket q) i HM
    rw [HL]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
      old_field_count hn ht ha hR0 q hv,new_field_count hn ht ha hR0 q hv]
    exact ⟨by omega,by omega⟩
  have HScan : IntegralMixedPhysicalFieldEqualityList.packet (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.word q) (context hn ht ha hR0 q) wF table∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
    apply (IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha (radius_binary hR0) _ _ _ _ table
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) hF HB).mpr
    intro i hi
    have HM : i<originalBirth hn ht ha hR0 q:=hi.trans_eq HTable
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup _ _ i HM]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    simpa only [originalField] using HFields i HM
  have HGuard:=query_guard hn ht ha hR0 q wP hv hd
  have HLeft:=endpoint_original hn ht ha hR0 q wP hv hd hp Hvalues false
  have HRight:=endpoint_original hn ht ha hR0 q wP hv hd hp Hvalues true
  simp only [Bool.false_eq_true,ite_false] at HLeft
  simp only [ite_true] at HRight
  have HReject : z∉IntegralMixedPhysicalCriticalInterval.language hn ht ha (radius_binary hR0) false:=by
    apply (IntegralMixedPhysicalChronologicalCritical.empty_iff hn ht ha (radius_binary hR0) false z (prefixRoot q) wP
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q) HG
      (query_packet_key hn ht ha hR0 q wP) hp HGuard (query_positive hn ht ha hR0 q wP)
      (t (IntegralMixedRoadmapAtomic.original q)).toData.size (query_degree hn ht ha hR0 q wP)).mpr
    apply Set.disjoint_left.mpr
    intro u hu hc
    have HU : u∈Ioo (originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
        (originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)):=by
      exact interval_transport HLeft HRight hu
    have HC : u∈originalCriticalValues hn ht ha hR0 q hv hd:=by
      have HE : u∈parentCriticalValues hn ht ha hR0 q wP hv hd hp:=by
        unfold parentCriticalValues
        exact hc
      exact (congrArg (fun s : Set ℝ=>u∈s) HSet).mp HE
    exact Set.disjoint_left.mp HF HU HC
  have hp' : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false) z wP:=by
    simpa only [z,query_parentWord] using hp
  have HFields' : fields hn ht ha hR0 (pair (pair q wF) wP)∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
    simpa only [fields,atomic,fullWord,pairFst_pair,pairSnd_pair,table] using HScan
  have HW : Witness hn ht ha hR0 (pair (pair q wF) wP):=by
    simpa only [Witness,critical,joint,atomic,parentWord,fullWord,pairFst_pair,pairSnd_pair] using
      (show IntegralMixedPhysicalCriticalInterval.Guard n false z ∧
        SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false false) z wP ∧
        SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false true) z wF ∧
        fields hn ht ha hR0 (pair (pair q wF) wP)∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0) ∧
        IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (radius_binary hR0) false (pair z wF) ∧
        z∉IntegralMixedPhysicalCriticalInterval.language hn ht ha (radius_binary hR0) false from
        ⟨HGuard,hp',hvF,HFields',HAgree,HReject⟩)
  have HRoot : pairFst z=pairFst (canonical hn ht ha hR0 q):=
    (root_word hn ht ha hR0 q wP).trans (root_word hn ht ha hR0 q []).symm
  have HWidth : SquareSampleCompleteVertices.width (input hn ht ha (radius_binary hR0) false true) z=
      fullWidth hn ht ha hR0 q:=by
    rw [IntegralMixedPhysicalCriticalContext.input_factor,
      SquareSampleCompleteNaturality.complete_width_comp]
    unfold fullWidth
    rw [IntegralMixedPhysicalCriticalContext.input_factor,
      SquareSampleCompleteNaturality.complete_width_comp,HRoot]
  exact ⟨wF,(Classical.choose hvF).1.trans HWidth,wP,hlen,HW⟩

/-- Actual coarse critical-freeness at the original word constructs both native
probe words internally. No interpreting hom or solvability premise is supplied. -/
theorem noCritical_of_original_critical_free (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (HF : OriginalSliceCriticalFree hn ht ha hR0 q hv hd) : NoCritical hn ht ha hR0 q :=by
  obtain ⟨wP,hp,hlen,Hvalues⟩:=exists_parent_word hn ht ha hR0 q hv
  exact noCritical_from_parent hn ht ha hR0 q hv hd HF wP hp hlen Hvalues

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
