/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendLayout
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
/-! # Exact old-prefix preservation in the concrete retained extension

The total record count, horizon and width are unchanged. Every shared prefix
has the same full state snapshot and the same natural row/bank observation.
The old complete word is used only to obtain its own natural tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

noncomputable def preparedRoot (old :List Bool) (producer :ℕ):=
  IntegralMixedRoadmapAtomic.root (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer [])
noncomputable def start (old :List Bool):=IntegralMixedRoadmapChain.rawStart
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.payload old)
  (IntegralMixedRoadmapAtomic.depth old)

theorem prepared_candidate (old :List Bool) (producer :ℕ):
    candidate (preparedRoot hn ht ha hR0 old producer)=candidate (IntegralMixedRoadmapAtomic.root old):=by
  simp only [preparedRoot,candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,candidate_packet]

theorem prepared_count (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old producer)=
      IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old):=by
  simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,pairFst_pair,pairSnd_pair] using
      raw_count hn ht ha hR0 old hv hd producer he

theorem prepared_cap (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).cap
      (preparedRoot hn ht ha hR0 old producer)=
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).cap
      (IntegralMixedRoadmapAtomic.root old):=
  IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 _ _ (prepared_candidate hn ht ha hR0 old producer)
    (prepared_count hn ht ha hR0 old hv hd producer he)

theorem start_fit (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old):
    start hn ht ha hR0 old≤IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old):=by
  simpa only [start,IntegralMixedMarkedPrefixTransfer.chainRoot,IntegralMixedRoadmapAtomic.root,
    IntegralMixedRoadmapAtomic.depth] using IntegralMixedMarkedPrefixTransfer.chain_prefix_good
      (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv) (IntegralMixedRoadmapAtomic.candidate old)

theorem prepared_record (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (producer i :ℕ) (hi :i<start hn ht ha hR0 old):
    IntegralMixedCausalRecordPlanBits.code (preparedRoot hn ht ha hR0 old producer) i=
      IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root old) i:=by
  simpa only [preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,
    IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
    pairFst_pair,pairSnd_pair] using prefix_record hn ht ha hR0 old hv producer i hi

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters preparedRoot start

theorem prefix_observation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
    (j :ℕ) (hj :j≤start hn ht ha hR0 old):
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) j
      ((hj.trans (start_fit hn ht ha hR0 old hv)).trans_eq (prepared_count hn ht ha hR0 old hv hd producer he).symm)=
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old) j
      (hj.trans (start_fit hn ht ha hR0 old hv)):=by
  exact IntegralMixedMarkedPrefixObservation.eq hn ht ha hR0 _ _
    (prepared_candidate hn ht ha hR0 old producer) (prepared_count hn ht ha hR0 old hv hd producer he) j _
    (fun i hi=>prepared_record hn ht ha hR0 old hv producer i (hi.trans_le hj))

theorem prefix_snapshot (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
    (j :ℕ) (hj :j≤start hn ht ha hR0 old):
    IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) j
      ((hj.trans (start_fit hn ht ha hR0 old hv)).trans_eq (prepared_count hn ht ha hR0 old hv hd producer he).symm)=
    IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old) j
      (hj.trans (start_fit hn ht ha hR0 old hv)):=by
  exact IntegralMixedMarkedPrefixSnapshot.eq hn ht ha hR0 _ _
    (prepared_candidate hn ht ha hR0 old producer) (prepared_count hn ht ha hR0 old hv hd producer he) j _
    (fun i hi=>prepared_record hn ht ha hR0 old hv producer i (hi.trans_le hj))

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
