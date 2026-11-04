/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendNativeHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
/-! # Exact meaningful windows in the retained-endpoint extension -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem fresh_last (d : ℕ) (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapChain.freshCount (payload d old e) (IntegralMixedRoadmapAtomic.depth old)=0:=by
  simp only [IntegralMixedRoadmapAtomic.depth,payload,IntegralMixedRoadmapChain.freshCount,
    IntegralMixedRoadmapChain.left,IntegralMixedRoadmapChain.right,IntegralMixedRoadmapChain.append_entry_last,
    IntegralMixedRoadmapChain.levelEntry,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,IntegralMixedRoadmapEndpointSyntax.fresh,
    endpoint,IntegralMixedRoadmapEndpointSyntax.field_spec_0,ite_true,Nat.add_zero]

theorem raw_start_last (d : ℕ) (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapChain.rawStart d (payload d old e) (IntegralMixedRoadmapAtomic.depth old)=
      IntegralMixedRoadmapChain.rawStart d (IntegralMixedRoadmapAtomic.payload old) (IntegralMixedRoadmapAtomic.depth old):=by
  unfold payload
  exact IntegralMixedRoadmapChain.append_rawStart_before d (IntegralMixedRoadmapAtomic.payload old)
    (endpoint e) (endpoint e) false (IntegralMixedRoadmapChain.seedCode d)
    (IntegralMixedRoadmapAtomic.depth old) (Nat.le_refl _)

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "Q"=>(fun old e=>packet (D old) old e [])
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapAtomic.depth
  payload preparedRoot

theorem finish_eq (old : List Bool) (e : ℕ) :
    finishBirth hn ht ha hR0 old e=beginBirth hn ht ha hR0 old+2+
      2*(D old-IntegralMixedRoadmapAtomic.depth old):=by
  unfold finishBirth beginBirth IntegralMixedRoadmapAtomic.endBirth
  rw [payload_packet,depth_packet,IntegralMixedRoadmapChain.rawStart_succ]
  rw [raw_start_last,IntegralMixedRoadmapChain.blockCount,fresh_last]
  omega

theorem midpoint_birth (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapProper.midBirth (D old) (N old) (Q old e)=beginBirth hn ht ha hR0 old:=by
  have HL : IntegralMixedRoadmapProper.levelIndex (Q old e)=IntegralMixedRoadmapAtomic.depth old:=by
    simp only [IntegralMixedRoadmapProper.levelIndex,depth_packet,Nat.add_sub_cancel]
  unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth IntegralMixedRoadmapChain.birth
  rw [payload_packet,HL,fresh_last]
  rw [raw_start_last]
  rfl

theorem midpoint_count (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapProper.captureCount (D old) (Q old e)=D old-IntegralMixedRoadmapAtomic.depth old:=by
  simp only [IntegralMixedRoadmapProper.captureCount,IntegralMixedRoadmapProper.levelIndex,depth_packet,
    Nat.add_sub_cancel]

theorem child_count (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapAtomic.free (D old) (Q old e)=D old-IntegralMixedRoadmapAtomic.depth old:=by
  simp only [IntegralMixedRoadmapAtomic.free,depth_packet,Nat.add_sub_add_right]

theorem child_anchor (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapAtomic.anchor (D old) (N old) (Q old e)=
      beginBirth hn ht ha hR0 old+1+(D old-IntegralMixedRoadmapAtomic.depth old):=by
  unfold IntegralMixedRoadmapAtomic.anchor
  change finishBirth hn ht ha hR0 old e-(_+1)=_
  rw [child_count,finish_eq]
  omega

theorem finish_le_full (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) :
    finishBirth hn ht ha hR0 old e≤fullBirth hn ht ha hR0 old e:=by
  have HC : IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old e)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (D old):=by
    rw [prepared_count hn ht ha hR0 old hv hd e he]
    simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using
        IntegralMixedRoadmapAtomic.raw_count hn ht ha hR0 old hv
  have HR:=IntegralMixedRoadmapChain.rawStart_bound (D old) (payload (D old) old e)
    (IntegralMixedRoadmapAtomic.depth old+1) (by omega)
  unfold finishBirth fullBirth IntegralMixedRoadmapAtomic.endBirth
  rw [payload_packet,depth_packet,initial_root,HC]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
