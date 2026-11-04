/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeComplete
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeHints
/-! # Ordinary parent bad heights are exactly original-only native probe witnesses

The literal checked raw-table domain and the base own full word are explicit.
Every prepared word is sampled afresh at the same target horizon and width.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedRoadmapBadProbeParent.snapshot IntegralMixedMarkedPrefixFieldReadback.parentPoint
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
private theorem banks_equal :IntegralMixedMarkedReservedParent.bank hn ht ha hR0=(B):=rfl
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank

variable (base : List Bool) (codes : List (List Bool)) (last : List Bool)
 (hraw :raw base=WordList.encode (codes++[last]))
 (hl :SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedMarkedPrefixFieldReadback.context (root base)) (word base))
local notation "VL"=>IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root base) (word base) hl
local notation "left"=>IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 base hl false
local notation "right"=>IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 base hl true

include hraw in
theorem complete
    (hp :∀side,producer side base<IntegralMixedMarkedPrefixFieldReadback.parent n (root base))
    (hbad :∃a∈Set.Ioo left right,a∈IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0 (root base) (word base) (labels base) hl) :
    ∃hint w,IntegralMixedRoadmapBadProbeTest.Witness hn ht ha (radius_binary hR0) (pair (pair base hint) w):=by
 obtain ⟨a,ha',hbad⟩:=hbad
 let d:=IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root base)
 have HC :0<count base:=by rw [IntegralMixedRoadmapBadProbeCanonical.count_eq base codes last hraw];omega
 have HCount :IntegralMixedCausalRecordPlanBits.count (root base)=count base:=by
   simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,root,count,pairFst_pair,pairSnd_pair]
 have HX :IntegralMixedHistory.Canonical d.state:=IntegralMixedRoadmapBadProbeParent.canonical hn ht ha hR0 (root base)
 obtain ⟨code,HD⟩:=(IntegralMixedPrefixSnapshot.Data.mem_bad_iff_coded d (labels base) VL HX a).mp hbad
 have HB:=IntegralMixedRoadmapBadProbeParent.packet_birth hn ht ha hR0 base HC
 rw [banks_equal hn ht ha hR0] at HB
 have HP :∀side,producer side base<d.birth:=fun side=>(hp side).trans_eq
   (IntegralMixedRoadmapBadProbeParent.birth hn ht ha hR0 (root base) (HC.trans_eq HCount.symm)).symm
 obtain ⟨hint,HH,HE,Hdegree⟩:=IntegralMixedPrefixSnapshot.Data.coded_hint d base VL a code
   ((B).parameters.ambient (root base)+5) HC HB (HP false) (HP true)
   (IntegralMixedRoadmapBadProbeParent.auxiliary_cap hn ht ha hR0 (root base)) HD
 let z:=pair base hint
 have HH' :HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
     (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
     (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z:=by
   simpa only [d,banks_equal hn ht ha hR0,IntegralMixedRoadmapBadProbeParent.ambient,IntegralMixedRoadmapBadProbeParent.width,
     IntegralMixedRoadmapBadProbeTest.dimension,IntegralMixedRoadmapBadProbeTest.initial,
     IntegralMixedRoadmapBadProbeTest.width,z,pairFst_pair] using HH
 have HE' :probe (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z) z=code:=by
   simpa only [d,banks_equal hn ht ha hR0,IntegralMixedRoadmapBadProbeParent.ambient,IntegralMixedRoadmapBadProbeTest.dimension,z,pairFst_pair] using HE
 have HD' :d.CodedFactor (labels base) VL a (probe (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z) z):=HE'.symm ▸ HD
 obtain ⟨w,HW⟩:=IntegralMixedRoadmapBadProbeComplete.at_hint_base hn ht ha hR0 z codes last base
   (pairFst_pair base hint) hraw hl a HH' HD' Hdegree ha'
 exact ⟨hint,w,HW⟩

include hraw in
theorem hasBadProbe_iff
    (hp :∀side,producer side base<IntegralMixedMarkedPrefixFieldReadback.parent n (root base))
    (hab :left<right) :
    IntegralMixedRoadmapBadProbeSearch.HasBadProbe hn ht ha (radius_binary hR0) base ↔
      ∃a∈Set.Ioo left right,a∈IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0 (root base) (word base) (labels base) hl:=by
 rw [IntegralMixedRoadmapBadProbeSearch.hasBadProbe_iff hn ht ha (radius_binary hR0)]
 constructor
 · rintro ⟨hint,hH⟩
   obtain ⟨w,HW⟩:=(IntegralMixedRoadmapBadProbeTest.hasWitness_iff hn ht ha (radius_binary hR0) (pair base hint)).mp hH
   have HL :SquareSampleCompleteVertices.Valid S
       (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst (pair base hint)))) (word (pairFst (pair base hint))):=by
     simpa only [pairFst_pair] using hl
   have HR:=IntegralMixedRoadmapBadProbeSound.ordinary_bad hn ht ha hR0 (pair base hint) w HL HW
     (by simpa only [pairFst_pair] using hab)
   simpa only [pairFst_pair] using HR
 · intro HBad
   obtain ⟨hint,w,HW⟩:=complete hn ht ha hR0 base codes last hraw hl hp HBad
   exact ⟨hint,(IntegralMixedRoadmapBadProbeTest.hasWitness_iff hn ht ha (radius_binary hR0) (pair base hint)).mpr ⟨w,HW⟩⟩

include hraw in
theorem noBadProbe_iff
    (hp :∀side,producer side base<IntegralMixedMarkedPrefixFieldReadback.parent n (root base))
    (hab :left<right) :
    IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha (radius_binary hR0) base ↔
      ∀a,a∈Set.Ioo left right→a∉IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0 (root base) (word base) (labels base) hl:=by
 rw [IntegralMixedRoadmapBadProbeSearch.NoBadProbe,hasBadProbe_iff hn ht ha hR0 base codes last hraw hl hp hab]
 simp only [not_exists,not_and]

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics
