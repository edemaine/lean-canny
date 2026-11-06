/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalPreparedParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalOriginalSlice
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCutStage
/-! # Construct native no-critical witnesses from the original frozen slice -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderCriticalPrefixes (key input positive)
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

private theorem family_source_heq (a : Parameters) (e : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (j : IntegralMixedFramedHistoryFamilyBits.Data a e) (key : List Bool) {n : ℕ}
    (q : SpatialSource n) (he : HEq (IntegralMixedFramedHistoryFamilyBits.instruction a e key).source q) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family a e j).spatial key) q := he

private theorem original_height_val (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    (originalHeight q hv hd).val=IntegralMixedRoadmapProper.levelIndex q := rfl

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "K"=>key false
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
 IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe

noncomputable local instance parentFintype (q : List Bool) : Fintype ((G).physical (K q)):=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0)
    (IntegralMixedFramedHistoryFamilyBits.commands P D (K q))))

private theorem full_word_at_critical (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
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
      (FormulaSignSlotRadialProviderCriticalInterval.parentValues q hp) h) :
    ∃w,∃_hv : SquareSampleCompleteVertices.Valid (input true) q w,
      FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q w) :=by
  let : Fintype ((G).physical (K q)):=parentFintype q
  have HInterpretation:=IntegralFramedPhysicalSquare.exists_interpretation P D H L F C hs K
    (positive false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp
  obtain ⟨φ,Hφ,Hvalues⟩:=HInterpretation
  have HV (i : Fin ((G).birth (K q))) :
      φ (((G).state (K q)).bank.numerator i)/(((G).state (K q)).bank.denominator i:ℝ)=
        FormulaSignSlotRadialProviderCriticalInterval.parentValues q hp i :=
    (Hvalues i).trans (IntegralFramedPhysicalSquare.bank_naturalPoint P D H L F C hs K
      (positive false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i).symm
  have HR:= (realCriticalWitness_iff ((G).state (K q))
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (K q)) ((G).birth_bound _)
    hn0 charge hd hcap frame HA HP HF h hh
    (IntegralFramedPhysicalSquare.rawPoint P D H L F C hs K
      (positive false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
    (IntegralFramedPhysicalSquare.raw_roots P D H L F C hs K
      (positive false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
    φ (by simpa only [IntegralFramedPhysicalSquare.rawPoint,Function.comp_apply] using Hφ)
    (FormulaSignSlotRadialProviderCriticalInterval.parentValues q hp) HV u).mpr hu
  have HN:= (FormulaSignSlotRadialProviderCriticalInterval.naturalWitness_iff_actual q
    frame HA h hh (FormulaSignSlotRadialProviderCriticalInterval.parentArray q hp)
    u hc φ HV).mpr HR
  obtain ⟨z,hz,hm,_,_⟩:=HN
  obtain ⟨w,hv,HZ⟩:=IntegralFramedPhysicalSquare.exists_joint_natural P D H L F C hs (key true)
    (positive true) q z hz
  refine ⟨w,hv,?_⟩
  apply (FormulaSignSlotRadialProviderCriticalInterval.agrees_iff_observations
    q w hp hv z HZ).mpr
  intro i hi
  let j : Fin ((G).birth (K q)):=⟨i,by
    rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false]
    exact hi⟩
  have HE:=IntegralMixedPhysicalCriticalObservation.retained_observation P D H (K q)
    (HA.pointData h h hh hh).rule z q
    (FormulaSignSlotRadialProviderCriticalInterval.parent_room q) hc j
  rw [←FormulaSignSlotRadialProviderCriticalInterval.child_key q] at HE
  exact (FormulaSignSlotRadialProviderCriticalInterval.bank_point_observation false q _ hp _
    (FormulaSignSlotRadialProviderCriticalInterval.parentArray_joint q hp) i hi).trans
      ((hm j).trans HE.symm)

private noncomputable def parentCriticalValues (q w : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid (input false)
      (query (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q w)))) : Set ℝ:=
  let z:=query (pair q w)
  let HG:=parent_point_good q w hv hd
  realCriticalValues ((G).spatial (K z))
    (line (IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1).frame
      ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)
    (FormulaSignSlotRadialProviderCriticalInterval.parentValues z hp)
    ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩

private theorem spatial_heq {a b : List Bool} (he : a=b) :
    HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial a) (FormulaSignSlotRadialProviderIntegerPlan.spatial b) :=by
  cases he
  rfl

attribute [local semireducible] FormulaSignSlotRadialProviderRecordPlan.bank in
private theorem parent_source_original (q w : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    HEq ((G).spatial (K (query (pair q w)))) (FormulaSignSlotRadialProviderAtomic.source q) :=by
  let k:=K (query (pair q w))
  have HC : FormulaSignSlotRadialProviderRecordPlan.providerContext (pairFst k)=
      FormulaSignSlotRadialProviderAtomic.provider q:=by
    simpa only [k,FormulaSignSlotRadialProviderRecordPlan.providerContext,
      FormulaSignSlotRadialProviderCriticalPrefixes.key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
      using query_provider q w
  have HS : HEq ((G).spatial k) (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst k)):=by
    have HE:=(FormulaSignSlotRadialProviderRecordPrefix.instruction_initial k).trans
      (FormulaSignSlotRadialProviderRecordPrefix.initial_source (pairFst k))
    have HF:=family_source_heq FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
      FormulaSignSlotRadialProviderRecordPlan.certifiedPlan FormulaSignSlotRadialProviderRecordPlan.certifiedData
      k (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst k)) (heq_of_eq HE)
    exact HF
  have HM : HEq (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst k))
      (FormulaSignSlotRadialProviderIntegerPlan.spatial (FormulaSignSlotRadialProviderAtomic.provider q)):=by
    unfold FormulaSignSlotRadialProviderRecordPlan.spatial
    exact spatial_heq HC
  have HA:=FormulaSignSlotRadialProviderAtomic.source_provider q hv
  have HB:=HM.trans HA.symm
  exact HS.trans HB

private theorem parent_critical_values_original (q w : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid (input false)
      (query (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q w))))
    (Hvalues : ∀i : Fin ((G).birth (K (query (pair q w)))),
      FormulaSignSlotRadialProviderCriticalInterval.parentValues
        (query (pair q w)) hp i=originalNaturalValues q hv i.val) :
    parentCriticalValues q w hv hd hp=originalCriticalValues q hv hd :=by
  have HD : (G).ambient (K (query (pair q w)))=originalAmbient q:=
    (query_key_dimension q w).trans (FormulaSignSlotRadialProviderAtomic.native_dimension q).symm
  have HM:=actual_parent_birth q w hv
  have HS:=parent_source_original q w hv
  unfold parentCriticalValues originalCriticalValues
  apply critical_values_congr _ _ HD HM HS (IntegralMixedRoadmapProper.labels q)
    (parent_point_good q w hv hd).1 (original_point_good q hv hd).1 _ _ (original_height_val q hv hd).symm
  intro i j hij
  exact (Hvalues i).trans (congrArg (originalField q hv)
    (congrArg (fun v : ℕ=>originalBirth q-1-v) hij))

private theorem producer_before_parent (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (side : Bool) : IntegralMixedRoadmapProper.producer side q<originalBirth q :=by
  have HG:=FormulaSignSlotRadialProviderProperCritical.midpoint_good q hv hd
  have HF:=FormulaSignSlotRadialProviderProperCritical.midpoint_fit q hv hd
  have HC : IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)):=by
    simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.packet,IntegralMixedRoadmapBadProbePacket.raw,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapAtomic.payload,FormulaSignSlotRadialProviderAtomic.payload]
  have HB : IntegralMixedRoadmapProper.midBirth (FormulaSignSlotRadialProviderAtomic.dimension q)
      (FormulaSignSlotRadialProviderAtomic.initial q) q=
      FormulaSignSlotRadialProviderAtomic.initial q+
        IntegralMixedRoadmapProper.midRawIndex (FormulaSignSlotRadialProviderAtomic.dimension q) q:=by
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HM : IntegralMixedRoadmapProper.midBirth (FormulaSignSlotRadialProviderAtomic.dimension q)
      (FormulaSignSlotRadialProviderAtomic.initial q) q≤originalBirth q:=by
    unfold originalBirth
    rw [HB,HC]
    omega
  cases side
  · exact HG.2.1.trans_le HM
  · exact HG.2.2.1.trans_le HM

private theorem query_guard (q w : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    FormulaSignSlotRadialProviderCriticalInterval.Guard (query (pair q w)) :=by
  refine ⟨critical_query q w,?_,?_⟩
  · have HE:=query_endpoint false q w
    simp only [Bool.false_eq_true,ite_false] at HE
    rw [HE,query_birth q w (count_positive q hv)]
    exact producer_before_parent q hv hd false
  · have HE:=query_endpoint true q w
    simp only [ite_true] at HE
    rw [HE,query_birth q w (count_positive q hv)]
    exact producer_before_parent q hv hd true

private theorem endpoint_original (q w : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid (input false)
      (query (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q w))))
    (Hvalues : ∀i : Fin ((G).birth (K (query (pair q w)))),
      FormulaSignSlotRadialProviderCriticalInterval.parentValues
        (query (pair q w)) hp i=originalNaturalValues q hv i.val)
    (side : Bool) :
    FormulaSignSlotRadialProviderCriticalInterval.endpointValue
      (query (pair q w)) hp
      (Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (query (pair q w))
        else IntegralMixedPhysicalCriticalQuery.leftWord (query (pair q w))))=
      originalField q hv (IntegralMixedRoadmapProper.producer side q) :=by
  rw [query_endpoint]
  have HB : FormulaSignSlotRadialProviderCriticalPrefixes.birth false (query (pair q w))=
      originalBirth q:=query_birth q w (count_positive q hv)
  have HP:=producer_before_parent q hv hd side
  let i : Fin ((G).birth (K (query (pair q w)))):=
    ⟨FormulaSignSlotRadialProviderCriticalPrefixes.birth false (query (pair q w))-1-
      IntegralMixedRoadmapProper.producer side q,by
      rw [actual_parent_birth q w hv,HB]
      omega⟩
  have HE : FormulaSignSlotRadialProviderCriticalInterval.endpointValue
      (query (pair q w)) hp (IntegralMixedRoadmapProper.producer side q)=
      FormulaSignSlotRadialProviderCriticalInterval.parentValues
        (query (pair q w)) hp i:=
    (FormulaSignSlotRadialProviderCriticalContext.parentValues_point _ hp i).symm
  have HR : originalBirth q-1-i.val=IntegralMixedRoadmapProper.producer side q:=by
    dsimp only [i]
    rw [HB]
    omega
  exact HE.trans ((Hvalues i).trans (congrArg (originalField q hv) HR))

private theorem old_field_count (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q)=
      originalBirth q+1 :=by
  rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
  simp only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair]
  change FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)+
    IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q)=_
  rw [base_count]
  have HP:=count_positive q hv
  unfold originalBirth FormulaSignSlotRadialProviderAtomic.initial
  omega

private theorem new_field_count (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    FormulaSignSlotRadialProviderFieldEquality.count (context q)=
      originalBirth q+1 :=by
  rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
  simp only [context,pairFst_pair]
  have HF:=FormulaSignSlotRadialProviderCriticalContext.full_birth (canonical q)
  have HS:=FormulaSignSlotRadialProviderCriticalPrefixes.consecutive (canonical q)
  have HP:=query_birth q [] (count_positive q hv)
  change FormulaSignSlotRadialProviderCriticalPrefixes.birth true (canonical q)=
    FormulaSignSlotRadialProviderRecordPlan.fullCount (root q) at HF
  rw [←HF,HS]
  simpa only [canonical,originalBirth] using congrArg (fun k : ℕ=>k+1) HP

private theorem field_context_congr (c d w : List Bool) (he : c=d)
    (hc : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderAtomic.input) c w)
    (hd : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderAtomic.input) d w)
    (i : ℕ) : FormulaSignSlotRadialProviderFieldEquality.point c w hc i=
      FormulaSignSlotRadialProviderFieldEquality.point d w hd i :=by
  subst d
  rfl

private theorem interval_transport {a b c d u : ℝ} (ha : a=c) (hb : b=d)
    (hu : u∈Ioo a b) : u∈Ioo c d :=by
  cases ha
  cases hb
  exact hu

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
 FormulaSignSlotRadialProviderAtomic.payload IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
 IntegralMixedRoadmapProper.labels originalField originalNaturalValues originalCriticalValues parentCriticalValues

private theorem noCritical_from_parent (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (HF : OriginalSliceCriticalFree q hv hd) (wP : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false)
      (query (pair q wP))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q wP))))
    (hlen : wP.length=parentWidth q)
    (Hvalues : ∀i : Fin ((G).birth (K (query (pair q wP)))),
      FormulaSignSlotRadialProviderCriticalInterval.parentValues
        (query (pair q wP)) hp i=originalNaturalValues q hv i.val) :
    NoCritical q :=by
  let z:=query (pair q wP)
  let HG:=parent_point_good q wP hv hd
  let d:=IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1
  let h : Fin ((P).ambient (pairFst (K z))+1):=⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩
  have HH : h∉d.frame.frozen:=by
    rw [d.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapProper.labels_count]
    exact Nat.lt_irrefl _
  have HC : (IntegralMixedFramedHistoryFamilyBits.instruction P D (K z)).command=
      .critical (d.atomic.pointData h h HH HH).rule:=
    FormulaSignSlotRadialProviderChronologicalCritical.command_key z (prefixRoot q) wP
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q) HG
      (query_packet_key q wP)
  have HSet:=parent_critical_values_original q wP hv hd hp Hvalues
  obtain ⟨u,HU⟩:=original_critical_nonempty q hv hd
  have HU' : u∈realCriticalValues ((G).spatial (K z)) (line d.frame h)
      (FormulaSignSlotRadialProviderCriticalInterval.parentValues z hp) h:=by
    have HE:=(congrArg (fun s : Set ℝ=>u∈s) HSet).mpr HU
    unfold parentCriticalValues at HE
    exact HE
  have HFull:=full_word_at_critical z hp d.frame d.atomic d.prefix_frozen d.free_normal h HH HC
    (query_positive q wP) (LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialProviderAtomic.original q)).toData.size
    (query_degree q wP) ((G).scalar_cap (K z)) u HU'
  obtain ⟨wF,hvF,HAgree⟩:=HFull
  have hCrit : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderAtomic.input)
      (FormulaSignSlotRadialProviderCriticalContext.context z) wF:=
    (FormulaSignSlotRadialProviderCriticalContext.valid_full z wF).mp hvF
  have hF : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderAtomic.input)
      (context q) wF:=by
    rw [←query_context q wP]
    exact hCrit
  have HBirth : FormulaSignSlotRadialProviderCriticalPrefixes.birth false z=originalBirth q:=
    query_birth q wP (count_positive q hv)
  have HFields : ∀i<originalBirth q,
      originalField q hv i=
        FormulaSignSlotRadialProviderFieldEquality.point (context q) wF hF i:=by
    intro i hi
    let j : Fin ((G).birth (K z)):=⟨originalBirth q-1-i,by
      rw [actual_parent_birth q wP hv]
      omega⟩
    have HJ : originalBirth q-1-j.val=i:=by dsimp only [j];omega
    have HP:=Hvalues j
    have HE:=FormulaSignSlotRadialProviderCriticalContext.parentValues_field z wF hp hvF hCrit HAgree j
    have HI : FormulaSignSlotRadialProviderCriticalPrefixes.birth false z-1-j.val=i:=by rw [HBirth];exact HJ
    rw [HI] at HE
    have HV : originalNaturalValues q hv j.val=originalField q hv i:=by
      unfold originalNaturalValues
      exact congrArg (originalField q hv) HJ
    exact (HV.symm.trans (HP.symm.trans HE)).trans
      (field_context_congr _ _ wF (query_context q wP) hCrit hF i)

  let table:=IntegralMixedRoadmapBadProbePacket.matchTable (FormulaSignSlotRadialProviderAtomic.initial q)
    (IntegralMixedRoadmapProper.badPacket q)
  have HTable : WordListRecords.count table=originalBirth q:=by
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_count]
    rfl
  have HB : ∀i<WordListRecords.count table,
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get table i)<
        FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q) ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get table i)<
        FormulaSignSlotRadialProviderFieldEquality.count (context q):=by
    intro i hi
    have HM : i<originalBirth q:=hi.trans_eq HTable
    have HL:=IntegralMixedRoadmapBadProbePacket.matchTable_lookup
      (FormulaSignSlotRadialProviderAtomic.initial q) (IntegralMixedRoadmapProper.badPacket q) i HM
    rw [HL]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
      old_field_count q hv,new_field_count q hv]
    exact ⟨by omega,by omega⟩
  have HScan : FormulaSignSlotRadialProviderFieldEqualityList.packet (FormulaSignSlotRadialProviderAtomic.context q)
      (FormulaSignSlotRadialProviderAtomic.word q) (context q) wF table∈
      FormulaSignSlotRadialProviderFieldEqualityList.language:=by
    apply (FormulaSignSlotRadialProviderFieldEqualityList.language_packet_iff _ _ _ _ table
      (FormulaSignSlotRadialProviderAtomic.full_valid q hv) hF HB).mpr
    intro i hi
    have HM : i<originalBirth q:=hi.trans_eq HTable
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup _ _ i HM]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    simpa only [originalField] using HFields i HM
  have HGuard:=query_guard q wP hv hd
  have HLeft:=endpoint_original q wP hv hd hp Hvalues false
  have HRight:=endpoint_original q wP hv hd hp Hvalues true
  simp only [Bool.false_eq_true,ite_false] at HLeft
  simp only [ite_true] at HRight
  have HReject : z∉FormulaSignSlotRadialProviderCriticalInterval.language:=by
    apply (FormulaSignSlotRadialProviderChronologicalCritical.empty_iff z (prefixRoot q) wP
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q) HG
      (query_packet_key q wP) hp HGuard (query_positive q wP)
      (LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialProviderAtomic.original q)).toData.size (query_degree q wP)).mpr
    apply Set.disjoint_left.mpr
    intro u hu hc
    have HU : u∈Ioo (originalField q hv (IntegralMixedRoadmapProper.producer false q))
        (originalField q hv (IntegralMixedRoadmapProper.producer true q)):=by
      exact interval_transport HLeft HRight hu
    have HC : u∈originalCriticalValues q hv hd:=by
      have HE : u∈parentCriticalValues q wP hv hd hp:=by
        unfold parentCriticalValues
        exact hc
      exact (congrArg (fun s : Set ℝ=>u∈s) HSet).mp HE
    exact Set.disjoint_left.mp HF HU HC
  have hp' : SquareSampleCompleteVertices.Valid (input false) z wP:=by
    simpa only [z,query_parentWord] using hp
  have HFields' : fields (pair (pair q wF) wP)∈
      FormulaSignSlotRadialProviderFieldEqualityList.language:=by
    simpa only [fields,atomic,fullWord,pairFst_pair,pairSnd_pair,table] using HScan
  have HW : Witness (pair (pair q wF) wP):=by
    simpa only [Witness,critical,joint,atomic,parentWord,fullWord,pairFst_pair,pairSnd_pair] using
      (show FormulaSignSlotRadialProviderCriticalInterval.Guard z ∧
        SquareSampleCompleteVertices.Valid (input false) z wP ∧
        SquareSampleCompleteVertices.Valid (input true) z wF ∧
        fields (pair (pair q wF) wP)∈FormulaSignSlotRadialProviderFieldEqualityList.language ∧
        FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair z wF) ∧
        z∉FormulaSignSlotRadialProviderCriticalInterval.language from
        ⟨HGuard,hp',hvF,HFields',HAgree,HReject⟩)
  have HRoot : pairFst z=pairFst (canonical q):=
    (root_word q wP).trans (root_word q []).symm
  have HWidth : SquareSampleCompleteVertices.width (input true) z=
      fullWidth q:=by
    rw [FormulaSignSlotRadialProviderCriticalContext.input_factor,
      SquareSampleCompleteNaturality.complete_width_comp]
    unfold fullWidth
    rw [FormulaSignSlotRadialProviderCriticalContext.input_factor,
      SquareSampleCompleteNaturality.complete_width_comp,HRoot]
  exact ⟨wF,(Classical.choose hvF).1.trans HWidth,wP,hlen,HW⟩

/-- Actual coarse critical-freeness at the original word constructs both native
probe words internally. No interpreting hom or solvability premise is supplied. -/
theorem noCritical_of_original_critical_free (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (HF : OriginalSliceCriticalFree q hv hd) : NoCritical q :=by
  obtain ⟨wP,hp,hlen,Hvalues⟩:=exists_parent_word q hv
  exact noCritical_from_parent q hv hd HF wP hp hlen Hvalues


theorem noCritical_original_slice_critical_free (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (HNo : NoCritical q) : OriginalSliceCriticalFree q hv hd :=by
  obtain ⟨wF,_,wP,_,HW⟩:=HNo
  obtain ⟨hp,HF⟩:=witness_coarse_critical_free q wF wP hv hd HW
  have HB : FormulaSignSlotRadialProviderCriticalPrefixes.birth false (query (pair q wP))=originalBirth q:=
    query_birth q wP (count_positive q hv)
  have HV : ∀i : Fin ((G).birth (K (query (pair q wP)))),
      FormulaSignSlotRadialProviderCriticalInterval.parentValues (query (pair q wP)) hp i=
        originalNaturalValues q hv i.val:=by
    intro i
    have HE:=witness_parent_fields q wF wP hv HW hp i
    rw [HB] at HE
    simpa only [originalNaturalValues,originalField] using HE
  have HS:=parent_critical_values_original q wP hv hd hp HV
  have HL:=witness_endpoint_field false q wF wP hv HW hp
  have HR:=witness_endpoint_field true q wF wP hv HW hp
  simp only [Bool.false_eq_true,ite_false] at HL
  simp only [ite_true] at HR
  have HF' : Disjoint (Ioo
      (FormulaSignSlotRadialProviderCriticalInterval.endpointValue (query (pair q wP)) hp
        (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord (query (pair q wP)))))
      (FormulaSignSlotRadialProviderCriticalInterval.endpointValue (query (pair q wP)) hp
        (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord (query (pair q wP))))))
      (parentCriticalValues q wP hv hd hp):=by
    simpa only [CoarseCriticalFree,parentCriticalValues] using HF
  rw [HL,HR,HS] at HF'
  simpa only [OriginalSliceCriticalFree,originalField] using HF'

theorem noCritical_iff_original_critical_free (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    NoCritical q ↔ OriginalSliceCriticalFree q hv hd :=
  ⟨noCritical_original_slice_critical_free q hv hd,noCritical_of_original_critical_free q hv hd⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
