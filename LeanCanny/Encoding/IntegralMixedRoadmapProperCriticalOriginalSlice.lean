/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNoCriticalSound
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
/-! # The no-critical converse uses only the original word's frozen slice -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
 IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry
 IntegralMixedRoadmapChain.frozen IntegralMixedRoadmapProper.labels originalField

noncomputable def originalBirth (q : List Bool):=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q+
  IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1

theorem original_point_good (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedChronologicalFrameCode.PointGood (n (IntegralMixedRoadmapAtomic.original q)+3)
      (originalBirth hn ht ha hR0 q) (IntegralMixedRoadmapProper.labels q)
      (IntegralMixedRoadmapProper.levelIndex q) (IntegralMixedRoadmapProper.levelIndex q) :=by
  have H:=coarse_point_good hn ht ha hR0 q [] hv hd
  rw [query_dimension,query_birth hn ht ha hR0 q [] (count_positive hn ht ha hR0 q hv),
    IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 q] at H
  exact H

noncomputable def originalDescriptor (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q):=
  IntegralMixedChronologicalFrameCode.descriptor (n (IntegralMixedRoadmapAtomic.original q)+3)
    (originalBirth hn ht ha hR0 q) (IntegralMixedRoadmapProper.labels q)
    (original_point_good hn ht ha hR0 q hv hd).1

noncomputable def originalValues (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i : Fin (originalBirth hn ht ha hR0 q)) : ℝ:=
  originalField hn ht ha hR0 q hv (originalBirth hn ht ha hR0 q-1-i.val)

noncomputable def originalHeight (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) : Fin (n (IntegralMixedRoadmapAtomic.original q)+3+1):=
  ⟨IntegralMixedRoadmapProper.levelIndex q,(original_point_good hn ht ha hR0 q hv hd).2.2.1⟩

noncomputable def originalCriticalValues (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) : Set ℝ:=
  realCriticalValues (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q))
    (line (originalDescriptor hn ht ha hR0 q hv hd).frame (originalHeight hn ht ha hR0 q hv hd))
    (originalValues hn ht ha hR0 q hv) (originalHeight hn ht ha hR0 q hv hd)

/-- A condition only on the original source, decoded coarse labels and original
full-word fields. No prepared parent word occurs in this definition. -/
noncomputable def OriginalSliceCriticalFree (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q) : Prop:=
  Disjoint (Ioo (originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
    (originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)))
    (originalCriticalValues hn ht ha hR0 q hv hd)

theorem original_slice_nonempty (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    (slice (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q))
      (originalDescriptor hn ht ha hR0 q hv hd).frame (originalValues hn ht ha hR0 q hv)).Nonempty :=by
  let p:=IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate q) q hv rfl
  have HP:=IntegralMixedRoadmapGraph.pointAt_occurrence hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate q) q hv rfl
  let d:=originalDescriptor hn ht ha hR0 q hv hd
  refine ⟨p,(d.slice_iff _ _ p).mpr ⟨HP.zero,?_⟩⟩
  intro i
  have HL : d.labels.length=IntegralMixedRoadmapProper.levelIndex q:=by
    dsimp only [d,originalDescriptor]
    rw [IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapProper.labels_count]
  have HI : i.val<IntegralMixedRoadmapProper.levelIndex q:=i.isLt.trans_eq HL
  have HDepth : i.val<IntegralMixedRoadmapAtomic.depth q:=by
    unfold IntegralMixedRoadmapProper.levelIndex at HI
    omega
  have HFrozen:=HP.frozen ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩ HDepth
  have HLabels : Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen q) i.val)=
      (d.labels[i]).val:=by
    have HE : Nat.fromBitsLE (WordList.get (IntegralMixedChronologicalFrameCode.labels d) i.val)=
        (d.labels[i]).val:=by
      simpa only [List.get_eq_getElem,Fin.getElem_fin] using IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt
    have HD : Nat.fromBitsLE (WordList.get (IntegralMixedChronologicalFrameCode.labels d) i.val)=
        Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i.val):=
      IntegralMixedChronologicalFrameCode.descriptor_lookup _ _ _ _ i.val
        (by rw [IntegralMixedRoadmapProper.labels_count];exact HI)
    have HF : Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen q) i.val)=
        Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i.val):=by
      simpa only [IntegralMixedRoadmapAtomic.frozen,IntegralMixedRoadmapProper.labels] using
        (IntegralMixedRoadmapChain.frozen_lookup (IntegralMixedRoadmapAtomic.payload q)
        (IntegralMixedRoadmapAtomic.depth q) i.val HDepth).trans
          (IntegralMixedRoadmapChain.frozen_lookup (IntegralMixedRoadmapAtomic.payload q)
            (IntegralMixedRoadmapProper.levelIndex q) i.val HI).symm
    exact HF.trans (HD.symm.trans HE)
  have HReverse : originalBirth hn ht ha hR0 q-1-(d.reference i).val=(d.labels[i]).val:=by
    have HB:=(d.labels[i]).isLt
    simp only [IntegralMixedChronologicalFrame.Descriptor.reference,Fin.val_mk]
    omega
  change p _=originalField hn ht ha hR0 q hv (originalBirth hn ht ha hR0 q-1-(d.reference i).val)
  rw [HReverse]
  simpa only [IntegralMixedRoadmapAtomic.levels,originalField,HLabels] using HFrozen

theorem original_critical_nonempty (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    (originalCriticalValues hn ht ha hR0 q hv hd).Nonempty :=by
  obtain ⟨p,hp⟩:=original_slice_nonempty hn ht ha hR0 q hv hd
  let d:=originalDescriptor hn ht ha hR0 q hv hd
  let h:=originalHeight hn ht ha hR0 q hv hd
  have HH : h∉d.frame.frozen:=by
    rw [d.frozen_mem]
    have HL : d.labels.length=IntegralMixedRoadmapProper.levelIndex q:=by
      dsimp only [d,originalDescriptor]
      rw [IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapProper.labels_count]
    rw [HL]
    exact Nat.lt_irrefl _
  obtain ⟨y,HY,HG⟩:=exists_component_critical_of_proper
    (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q))
    d.frame (originalValues hn ht ha hR0 q hv) h HH
    (IntegralMixedRoadmapGraph.original_proper (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate q)) p hp
  refine ⟨y h,?_⟩
  exact (line_realCriticalValues_iff _ d.frame _ h HH d.free_normal _).mpr
    ⟨y,connectedComponentIn_subset _ _ HY,rfl,HG⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
