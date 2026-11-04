/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalParentContext
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalOriginalSlice
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBadSound
public import LeanCanny.Encoding.IntegralMixedMarkedReservedPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalRealizedVertex
/-! # Allocate the actual reserved critical parent with the original bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedMarkedPrefixRun (reservedRoot)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def RealizedAt (B : IntegralFramedBankQuery.Bank) (key : List Bool) (values : ℕ→ℝ) : Prop:=
  IntegralMixedIntegerRealization.Realizes
    ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).state key) values

private theorem realized_congr {a S B m : ℕ} {P : SpatialSource a} {ι : Type}
    (x : State P S B m ι) (v w : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes x v) (he : ∀i<m,v i=w i) :
    IntegralMixedIntegerRealization.Realizes x w :=by
  obtain ⟨y,φ,hy,hφ,hv⟩:=hv
  exact ⟨y,φ,hy,hφ,fun i=>(hv i).trans (he i.val i.isLt)⟩

private theorem realizes_view (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedFamilyRunView.stateView P D H key) v) :
    IntegralMixedIntegerRealization.Realizes ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) v:=hv

private theorem realized_at_congr (A B : IntegralFramedBankQuery.Bank) (hB : A=B)
    (a b : List Bool) (hk : a=b) (values : ℕ→ℝ) (HR : RealizedAt A a values) :
    RealizedAt B b values :=by
  cases hB
  cases hk
  exact HR

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "K"=>IntegralMixedPhysicalCriticalPrefixes.key n false false
local notation "I"=>IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
 IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry
 IntegralMixedRoadmapChain.frozen IntegralMixedRoadmapProper.labels originalField

attribute [local irreducible] RealizedAt

private theorem banks_equal : BP=B:=by
  unfold IntegralMixedMarkedReservedParent.bank IntegralMixedPhysicalMarkedPlan.bank
  rfl

private theorem base_root (q : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : IntegralMixedRoadmapBadProbePacket.raw (IntegralMixedRoadmapProper.badPacket q)=WordList.encode (codes++[last])) :
    IntegralMixedRoadmapAtomic.root q=reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last [] :=by
  have HE:=IntegralMixedRoadmapBadProbeCanonical.root_eq (IntegralMixedRoadmapProper.badPacket q) codes last hr
  have HB:= (IntegralMixedRoadmapProper.badPacket_root q).symm.trans HE
  simpa only [IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair] using HB

private def probeAux (q : List Bool):=pair [] (pair
  (BinaryNatCode.encode (IntegralMixedRoadmapProper.producer false q))
  (BinaryNatCode.encode (IntegralMixedRoadmapProper.producer true q)))

private theorem prepared_root (q : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : IntegralMixedRoadmapBadProbePacket.raw (IntegralMixedRoadmapProper.badPacket q)=WordList.encode (codes++[last])) :
    root hn ht ha hR0 q=reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes
      (IntegralMixedPhysicalCriticalQuery.normalize (code hn ht ha hR0 q)) (probeAux q) :=by
  have HP : IntegralMixedRoadmapBadProbePacket.prefixWord (IntegralMixedRoadmapProper.badPacket q)=WordList.encode codes:=by
    rw [IntegralMixedRoadmapBadProbePacket.prefixWord,IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq _ codes last hr]
  unfold root canonical query
  simp only [IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    pairFst_pair,pairSnd_pair,IntegralMixedPhysicalCriticalQuery.prepare,
    IntegralMixedPhysicalCriticalQuery.withEndpoints,prefixRoot,IntegralMixedCausalRecordPlanBits.records,
    pairFst_pair,pairSnd_pair]
  rw [HP,IntegralMixedPhysicalCriticalQuery.snoc_encode]
  rfl

private theorem initial_reserved (q : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :
    number n (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes probe aux)+8=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q :=by
  rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 q]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,reservedRoot,pairFst_pair,
    IntegralMixedRoadmapAtomic.original]

private theorem prefix_birth (q : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : IntegralMixedRoadmapBadProbePacket.raw (IntegralMixedRoadmapProper.badPacket q)=WordList.encode (codes++[last])) :
    originalBirth hn ht ha hR0 q=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q+codes.length :=by
  unfold originalBirth
  rw [IntegralMixedRoadmapBadProbeCanonical.count_eq _ codes last hr]
  omega

noncomputable def originalNaturalValues (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i : ℕ) : ℝ:=originalField hn ht ha hR0 q hv (originalBirth hn ht ha hR0 q-1-i)

theorem canonical_parent_realizes (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    IntegralMixedIntegerRealization.Realizes ((G).state (K (canonical hn ht ha hR0 q)))
      (originalNaturalValues hn ht ha hR0 q hv) :=by
  obtain ⟨codes,last,hraw⟩:=IntegralMixedRoadmapLocalFrame.bad_raw_domain hn ht ha hR0 q hv
  have HB:=base_root q codes last hraw
  have HRoot:=prepared_root hn ht ha hR0 q codes last hraw
  let probe:=IntegralMixedPhysicalCriticalQuery.normalize (code hn ht ha hR0 q)
  let aux:=probeAux q
  have HV : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last []))
      (IntegralMixedRoadmapAtomic.word q):=by
    rw [IntegralMixedMarkedReservedPoint.input_eq hn ht ha hR0,←HB]
    exact IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv
  let v:=IntegralMixedMarkedReservedParent.values hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate q) codes last [] (IntegralMixedRoadmapAtomic.word q) HV
  have HR : RealizedAt BP (IntegralMixedFramedHistoryFamilyBits.keyAt
      (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes probe aux)
      (number n (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes probe aux)+8+codes.length)
      (canonical hn ht ha hR0 q)) v:=by
    unfold RealizedAt
    exact realizes_view _ _ _ _ _ (IntegralMixedMarkedReservedParent.prepared_canonical_realizes hn ht ha hR0
      (IntegralMixedRoadmapAtomic.candidate q) codes last [] (IntegralMixedRoadmapAtomic.word q) HV probe aux (canonical hn ht ha hR0 q))
  have HK : K (canonical hn ht ha hR0 q)=IntegralMixedFramedHistoryFamilyBits.keyAt
      (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes probe aux)
      (number n (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes probe aux)+8+codes.length)
      (canonical hn ht ha hR0 q):=by
    have HBirth : IntegralMixedPhysicalCriticalPrefixes.birth n false false (canonical hn ht ha hR0 q)=
        number n (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes probe aux)+8+codes.length:=
      (query_birth hn ht ha hR0 q [] (count_positive hn ht ha hR0 q hv)).trans
        ((prefix_birth hn ht ha hR0 q codes last hraw).trans
          (congrArg (fun k : ℕ=>k+codes.length) (initial_reserved hn ht ha hR0 q codes probe aux).symm))
    exact congrArg₂ (fun r b=>IntegralMixedFramedHistoryFamilyBits.keyAt r b (canonical hn ht ha hR0 q))
      HRoot HBirth
  have HReal : IntegralMixedIntegerRealization.Realizes ((G).state (K (canonical hn ht ha hR0 q))) v:=by
    have HR':=realized_at_congr BP B (banks_equal hn ht ha hR0) _ _ HK.symm v HR
    unfold RealizedAt at HR'
    exact HR'
  apply realized_congr _ v _ HReal
  intro i hi
  have HC:=count_positive hn ht ha hR0 q hv
  have HM : (G).birth (K (canonical hn ht ha hR0 q))=originalBirth hn ht ha hR0 q:=
    (IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha (radius_binary hR0) false false _).trans
      (query_birth hn ht ha hR0 q [] HC)
  have HI : i<originalBirth hn ht ha hR0 q:=hi.trans_eq HM
  have HO:=IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate q) codes last [] (IntegralMixedRoadmapAtomic.word q) HV
  have HOld : IntegralMixedMarkedPrefixFieldReadback.parent n (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last [])=
      originalBirth hn ht ha hR0 q:=by
    unfold IntegralMixedMarkedPrefixFieldReadback.parent
    rw [IntegralMixedMarkedPrefixRun.reserved_count,initial_reserved hn ht ha hR0,
      prefix_birth hn ht ha hR0 q codes last hraw]
    omega
  have HOld' : IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)=
      originalBirth hn ht ha hR0 q:=by rw [HB];exact HOld
  have HP:=IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
    (reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last []) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedMarkedReservedPoint.native_valid hn ht ha hR0 _ _ _ _ _ HV)
    (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega) i (HI.trans_eq HOld.symm)
  have HE:= (congrFun HO i).trans HP
  simpa only [v,HOld,HOld',←HB,IntegralMixedMarkedPrefixFieldReadback.context,
    IntegralMixedRoadmapAtomic.context,originalField,originalNaturalValues] using HE

theorem actual_parent_birth (q w : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    (G).birth (K (query hn ht ha hR0 (pair q w)))=originalBirth hn ht ha hR0 q :=
  (IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha (radius_binary hR0) false false _).trans
    (query_birth hn ht ha hR0 q w (count_positive hn ht ha hR0 q hv))

/-- The word is chosen at the canonical root first, then placed in the query.
Same-root input naturality preserves its entire tuple and bank readback. -/
theorem exists_parent_word (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    ∃w,∃hp : SquareSampleCompleteVertices.Valid I (query hn ht ha hR0 (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q w))),
      w.length=parentWidth hn ht ha hR0 q ∧
      ∀i : Fin ((G).birth (K (query hn ht ha hR0 (pair q w)))),
        IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false
          (query hn ht ha hR0 (pair q w)) hp i=
            originalNaturalValues hn ht ha hR0 q hv i.val :=by
  have HReal:=canonical_parent_realizes hn ht ha hR0 q hv
  obtain ⟨w,hp0,hlen,HP⟩:=IntegralFramedPhysicalSquare.exists_realized P D H L F C hs K
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha (radius_binary hR0) false false)
    (canonical hn ht ha hR0 q) (originalNaturalValues hn ht ha hR0 q hv) HReal
  have HE : pairFst (canonical hn ht ha hR0 q)=pairFst (query hn ht ha hR0 (pair q w)):=
    (root_word hn ht ha hR0 q []).trans (root_word hn ht ha hR0 q w).symm
  have hp' : SquareSampleCompleteVertices.Valid I (query hn ht ha hR0 (pair q w)) w:=
    (IntegralMixedPhysicalCriticalParentContext.valid_iff hn ht ha (radius_binary hR0) _ _ w HE).mp hp0
  have hp : SquareSampleCompleteVertices.Valid I (query hn ht ha hR0 (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q w))):=by
    rw [query_parentWord]
    exact hp'
  refine ⟨w,hp,hlen,?_⟩
  intro i
  have HB : (G).birth (K (canonical hn ht ha hR0 q))=
      (G).birth (K (query hn ht ha hR0 (pair q w))):=
    (actual_parent_birth hn ht ha hR0 q [] hv).trans (actual_parent_birth hn ht ha hR0 q w hv).symm
  let j : Fin ((G).birth (K (canonical hn ht ha hR0 q))):=⟨i.val,i.isLt.trans_eq HB.symm⟩
  have HT:=IntegralMixedPhysicalCriticalParentContext.point_eq hn ht ha (radius_binary hR0)
    (canonical hn ht ha hR0 q) (query hn ht ha hR0 (pair q w)) w HE hp0 hp' j i rfl
  have HPoint : IntegralFramedPhysicalSquare.point P D H L F C hs K
      (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha (radius_binary hR0) false false)
      (query hn ht ha hR0 (pair q w)) w hp' i=originalNaturalValues hn ht ha hR0 q hv i.val:=
    HT.symm.trans (HP j)
  have HPoint' : IntegralFramedPhysicalSquare.point P D H L F C hs K
      (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha (radius_binary hR0) false false)
      (query hn ht ha hR0 (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query hn ht ha hR0 (pair q w))) hp i=
        originalNaturalValues hn ht ha hR0 q hv i.val:=by
    simpa only [query_parentWord] using HPoint
  exact (IntegralFramedPhysicalSquare.bank_naturalPoint P D H L F C hs K
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha (radius_binary hR0) false false)
    (query hn ht ha hR0 (pair q w)) _ hp i).trans HPoint'

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
