/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLayout
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
/-! # A general endpoint append preserves every earlier actual prefix

Total record count and resources are derived from explicit endpoint syntax.
No word, interpretation or guard receipt is transported between roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

noncomputable def preparedRoot (old :List Bool) (l r :List Bool) (side :Bool):=
  IntegralMixedRoadmapAtomic.root (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old l r side [])
noncomputable def start (old :List Bool):=IntegralMixedRoadmapChain.rawStart
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.payload old)
  (IntegralMixedRoadmapAtomic.depth old)

theorem prepared_candidate (old :List Bool) (l r :List Bool) (side :Bool):
    candidate (preparedRoot hn ht ha hR0 old l r side)=candidate (IntegralMixedRoadmapAtomic.root old):=by
  simp only [preparedRoot,candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,candidate_packet]

theorem prepared_number (old l r :List Bool) (side :Bool):
    IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old l r side)=
      n (IntegralMixedRoadmapAtomic.original old):=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]

theorem prepared_dimension (old l r :List Bool) (side :Bool):
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient
      (preparedRoot hn ht ha hR0 old l r side)=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old l r side)+3=_
  rw [prepared_number,IntegralMixedRoadmapAtomic.dimension_eq]

theorem prepared_initial (old l r :List Bool) (side :Bool):
    IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot hn ht ha hR0 old l r side)+8=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old:=by
  rw [prepared_number,IntegralMixedRoadmapAtomic.initial_eq]

noncomputable def beginBirth (old :List Bool):=IntegralMixedRoadmapAtomic.endBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old

theorem begin_eq_start (old l r :List Bool) (side :Bool):
    beginBirth hn ht ha hR0 old=IntegralMixedAuxiliaryMarkedIntegerSource.number n
      (preparedRoot hn ht ha hR0 old l r side)+8+start hn ht ha hR0 old:=by
  rw [prepared_initial]
  rfl

theorem prepared_count (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r):
    IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old l r side)=
      IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old):=by
  simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,pairFst_pair,pairSnd_pair] using
      raw_count hn ht ha hR0 old hv hd l r side hE

theorem prepared_cap (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r):
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).cap
      (preparedRoot hn ht ha hR0 old l r side)=
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).cap
      (IntegralMixedRoadmapAtomic.root old):=
  IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 _ _ (prepared_candidate hn ht ha hR0 old l r side)
    (prepared_count hn ht ha hR0 old hv hd l r side hE)

theorem start_fit (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old):
    start hn ht ha hR0 old≤IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old):=by
  simpa only [start,IntegralMixedMarkedPrefixTransfer.chainRoot,IntegralMixedRoadmapAtomic.root,
    IntegralMixedRoadmapAtomic.depth] using IntegralMixedMarkedPrefixTransfer.chain_prefix_good
      (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv) (IntegralMixedRoadmapAtomic.candidate old)

theorem prepared_start_fit (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r):
    start hn ht ha hR0 old≤IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old l r side):=
  (start_fit hn ht ha hR0 old hv).trans_eq (prepared_count hn ht ha hR0 old hv hd l r side hE).symm

theorem prepared_record (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (i :ℕ) (hi :i<start hn ht ha hR0 old):
    IntegralMixedCausalRecordPlanBits.code (preparedRoot hn ht ha hR0 old l r side) i=
      IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root old) i:=by
  simpa only [preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,
    IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
    pairFst_pair,pairSnd_pair] using prefix_record hn ht ha hR0 old hv l r side i hi

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters preparedRoot start

theorem prefix_observation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r)
    (j :ℕ) (hj :j≤start hn ht ha hR0 old):
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old l r side) j
      ((hj.trans (start_fit hn ht ha hR0 old hv)).trans_eq (prepared_count hn ht ha hR0 old hv hd l r side hE).symm)=
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old) j
      (hj.trans (start_fit hn ht ha hR0 old hv)):=by
  exact IntegralMixedMarkedPrefixObservation.eq hn ht ha hR0 _ _
    (prepared_candidate hn ht ha hR0 old l r side) (prepared_count hn ht ha hR0 old hv hd l r side hE) j _
    (fun i hi=>prepared_record hn ht ha hR0 old hv l r side i (hi.trans_le hj))

theorem prefix_snapshot (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r)
    (j :ℕ) (hj :j≤start hn ht ha hR0 old):
    IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 (preparedRoot hn ht ha hR0 old l r side) j
      ((hj.trans (start_fit hn ht ha hR0 old hv)).trans_eq (prepared_count hn ht ha hR0 old hv hd l r side hE).symm)=
    IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old) j
      (hj.trans (start_fit hn ht ha hR0 old hv)):=by
  exact IntegralMixedMarkedPrefixSnapshot.eq hn ht ha hR0 _ _
    (prepared_candidate hn ht ha hR0 old l r side) (prepared_count hn ht ha hR0 old hv hd l r side hE) j _
    (fun i hi=>prepared_record hn ht ha hR0 old hv l r side i (hi.trans_le hj))

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
