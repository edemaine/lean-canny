/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapMidSignatureLookup
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointFrame
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedCriticalTail
/-! # Every paired MID signature producer precedes the child anchor -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.Valid

theorem signature_bounded_before_child (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd :0<IntegralMixedRoadmapAtomic.depth q)
    (idx :ℕ) (hidx :idx<D q+2):
    Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 q) idx)<
      IntegralMixedRoadmapAtomic.anchor (D q) (I q) q:=by
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  have HK :IntegralMixedRoadmapProper.levelIndex q≤D q:=by
    unfold IntegralMixedRoadmapProper.levelIndex
    omega
  have HG:=IntegralMixedRoadmapProper.midpoint_good hn ht ha hR0 q hv hd
  have HA:=(IntegralMixedRoadmapCheckedCriticalTail.latest_layout (initial:=I q) HD hd).2.2
  unfold ownSignature
  by_cases hi :idx<D q+1
  · by_cases hf :idx<IntegralMixedRoadmapProper.levelIndex q
    · rw [signature_lookup_frozen _ _ _ idx hf HK]
      have HF:=HG.1.2 idx (by rw [IntegralMixedRoadmapProper.labels_count];exact hf)
      omega
    · by_cases heq :idx=IntegralMixedRoadmapProper.levelIndex q
      · rw [heq,signature_lookup_left _ _ _ HK]
        have HL:=HG.2.1
        omega
      · have HGT :IntegralMixedRoadmapProper.levelIndex q < idx:=by omega
        rw [signature_lookup_free _ _ _ idx HGT (by omega)]
        unfold IntegralMixedRoadmapProper.midProducer IntegralMixedRoadmapProper.midFirst
        unfold IntegralMixedRoadmapProper.captureCount at HA
        omega
  · have HE :idx=D q+1:=by omega
    rw [HE,signature_lookup_right]
    have HR:=HG.2.2.1
    omega

theorem child_anchor_bounded_full (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd :0<IntegralMixedRoadmapAtomic.depth q):
    IntegralMixedRoadmapAtomic.anchor (D q) (I q) q<
      IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q):=by
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  have HL:=IntegralMixedRoadmapCheckedCriticalTail.latest_layout (initial:=I q) HD hd
  have HR:=IntegralMixedRoadmapChain.rawStart_bound (D q) (IntegralMixedRoadmapAtomic.payload q)
    (IntegralMixedRoadmapAtomic.depth q) (by omega)
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q)):=
    IntegralMixedFramedHistoryFamilyBits.family_birth (B).parameters (B).plan (B).data _
  rw [HC,IntegralMixedRoadmapCheckedProperMetadata.full_prefix hn ht ha hR0 q,
    IntegralMixedRoadmapAtomic.raw_count hn ht ha hR0 q hv]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  unfold IntegralMixedRoadmapAtomic.endBirth at HL
  omega

theorem signature_bounded_full (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd :0<IntegralMixedRoadmapAtomic.depth q)
    (idx :ℕ) (hidx :idx<D q+2):
    Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 q) idx)<
      IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q):=
  (signature_bounded_before_child hn ht ha hR0 q hv hd idx hidx).trans
    (child_anchor_bounded_full hn ht ha hR0 q hv hd)

end LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
