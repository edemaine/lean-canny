/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendReadback
/-! # A new full word changes neither the appended root nor its layout -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "Q"=>(fun old e=>packet (D old) old e [])
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot context

theorem packet_root (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapAtomic.root (packet (D old) old e w)=preparedRoot hn ht ha hR0 old e:=by
  simp only [preparedRoot,IntegralMixedRoadmapAtomic.root,candidate_packet,payload_packet]

theorem packet_context (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapAtomic.context (packet (D old) old e w)=context hn ht ha hR0 old e:=by
  rw [IntegralMixedRoadmapAtomic.context,packet_root]
  unfold context
  rfl

theorem packet_companion_query (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapAtomic.companionQuery (D (packet (D old) old e w)) (N (packet (D old) old e w))
      (packet (D old) old e w)=
      pair (pair (context hn ht ha hR0 old e) w)
        (IntegralMixedPhysicalPointCompanionScan.descriptor
          (IntegralMixedRoadmapAtomic.anchor (D old) (N old) (Q old e))
          (IntegralMixedRoadmapAtomic.first (D old) (N old) (Q old e))
          (IntegralMixedRoadmapAtomic.free (D old) (Q old e))):=by
  have HA : IntegralMixedRoadmapAtomic.anchor (D old) (N old) (packet (D old) old e w)=
      IntegralMixedRoadmapAtomic.anchor (D old) (N old) (Q old e):=by
    simp only [IntegralMixedRoadmapAtomic.anchor,IntegralMixedRoadmapAtomic.endBirth,
      IntegralMixedRoadmapAtomic.free,payload_packet,depth_packet]
  have HF : IntegralMixedRoadmapAtomic.first (D old) (N old) (packet (D old) old e w)=
      IntegralMixedRoadmapAtomic.first (D old) (N old) (Q old e):=by
    unfold IntegralMixedRoadmapAtomic.first
    rw [HA]
  have HK : IntegralMixedRoadmapAtomic.free (D old) (packet (D old) old e w)=
      IntegralMixedRoadmapAtomic.free (D old) (Q old e):=by
    simp only [IntegralMixedRoadmapAtomic.free,depth_packet]
  simp only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.companionQuery,
    IntegralMixedRoadmapAtomic.sampleQuery,packet_context,word_packet,HA,HF,HK]

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
