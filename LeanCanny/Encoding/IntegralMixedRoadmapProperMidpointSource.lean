/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointFrame
/-! # The actual midpoint and child records use the same original source -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0

noncomputable def midpointSource (q : List Bool):=
  (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan
    (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q))) (midBirth (D q) (N q) q)).source

private theorem source_root_transport (P : IntegralCriticalHistoryTask.Parameters)
    (plan0 : IntegralMixedFramedHistoryFamilyBits.Plan P) (r s : List Bool) (he : r=s) (i j : ℕ)
    (H : (IntegralMixedFramedRootPullback.instructionAt P plan0 r i).source=
      (IntegralMixedFramedRootPullback.instructionAt P plan0 r j).source) :
    (IntegralMixedFramedRootPullback.instructionAt P plan0 s i).source=
      (IntegralMixedFramedRootPullback.instructionAt P plan0 s j).source :=by subst s;exact H

theorem midpoint_source_eq_own (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    midpointSource hn ht ha hR0 q=IntegralMixedRoadmapAtomic.source hn ht ha hR0 q :=by
  have HI : midRawIndex (D q) q<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q):=by
    simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using midpoint_fit hn ht ha hR0 q hv hd
  have HN : IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8=N q:=by
    rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,
      IntegralMixedRoadmapAtomic.original]
  have HB : midBirth (D q) (N q) q=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8+midRawIndex (D q) q:=by
    unfold midBirth baseBirth IntegralMixedRoadmapChain.birth midRawIndex
    rw [HN]
    omega
  have HS:=IntegralMixedMarkedRecordReceipt.source_at hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)
    (midRawIndex (D q) q) (midBirth (D q) (N q) q) HI HB
  have HO:=IntegralMixedRoadmapAtomic.own_creating_source hn ht ha hR0 q hv
  have HE : (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan (IntegralMixedRoadmapAtomic.root q)
      (midBirth (D q) (N q) q)).source=
      (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan (IntegralMixedRoadmapAtomic.root q)
        (IntegralMixedRoadmapAtomic.endBirth (D q) (N q) q-1)).source:=HS.trans HO.symm
  have HT:=source_root_transport (BK).parameters (BK).plan (IntegralMixedRoadmapAtomic.root q)
    (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q)))
    (IntegralMixedRoadmapAtomic.context_root hn ht ha hR0 q).symm _ _ HE
  exact HT

theorem midpoint_source_original (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    HEq (midpointSource hn ht ha hR0 q)
      (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q)) :=
  (heq_of_eq (midpoint_source_eq_own hn ht ha hR0 q hv hd)).trans
    (IntegralMixedRoadmapAtomic.source_original hn ht ha hR0 q hv)

end LeanCanny.Encoding.IntegralMixedRoadmapProper
