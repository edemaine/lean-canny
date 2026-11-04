/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendConstruct
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendOwnPoint
public import LeanCanny.Encoding.IntegralMixedRoadmapEdge
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphCoding
/-! # Every accepted vertex has an actual identity extension at the next depth -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapRetainedAppend
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cast_identity_point_heq {a b :ℕ} (h :a=b) (p :Fin (a+1)→ℝ) :
    HEq (fun i :Fin (b+1)=>p (Fin.cast (congrArg (·+1) h).symm i)) p:=by
  cases h
  rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "V"=>IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
local notation "A"=>IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.point ownPoint

private theorem identity_point_heq (q :List Bool) (hv :V q) :
    HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv):=by
  unfold IntegralMixedRoadmapIdentity.point
  exact cast_identity_point_heq (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q) _

/-- The new vertex is accepted in its own context and has a native identity
edge to the old vertex; equality of geometric points alone is not an edge input. -/
theorem exists_identity_extension (old :List Bool) (hv :V old)
    (hd :IntegralMixedRoadmapAtomic.depth old<D old) :
    ∃q,∃hq :V q,
      IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.depth old+1 ∧
      D q=D old ∧
      IntegralMixedRoadmapAtomic.candidate q=IntegralMixedRoadmapAtomic.candidate old ∧
      A old q ∧
      HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
        (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq):=by
  let e:=IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
  let he:=own_endpoint_fit hn ht ha hR0 old
  have HE:=own_point_eligible hn ht ha hR0 old hv hd
  obtain ⟨w,hNew,_,HP⟩:=exists_valid_at hn ht ha hR0 old hv hd e he
    (ownPoint hn ht ha hR0 old hv) HE.1 HE.2.1 HE.2.2
  let q:=packet (D old) old e w
  have HC :IntegralMixedRoadmapAtomic.candidate q=IntegralMixedRoadmapAtomic.candidate old:=
    candidate_packet _ _ _ _
  have HPoint :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
      (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hNew):=
    (ownPoint_heq hn ht ha hR0 old hv).symm.trans HP.symm
  have HA :A old q:=IntegralMixedRoadmapEdge.of_same_point hn ht ha hR0 old q hv hNew HC.symm
    ((identity_point_heq hn ht ha hR0 old hv).trans
      (HPoint.trans (identity_point_heq hn ht ha hR0 q hNew).symm))
  exact ⟨q,hNew,depth_packet _ _ _ _,dimension_packet hn ht ha hR0 _ _ _ _,HC,HA,HPoint⟩

theorem exists_identity_extension_by (k :ℕ) (old :List Bool) (hv :V old)
    (hk :IntegralMixedRoadmapAtomic.depth old+k≤D old) :
    ∃q,∃hq :V q,
      IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.depth old+k ∧
      D q=D old ∧
      IntegralMixedRoadmapAtomic.candidate q=IntegralMixedRoadmapAtomic.candidate old ∧
      Relation.ReflTransGen A old q ∧
      HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
        (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq):=by
  induction k generalizing old with
  | zero=>exact ⟨old,hv,by omega,rfl,rfl,.refl,HEq.rfl⟩
  | succ k ih=>
    obtain ⟨next,hNext,HD,HDim,HC,HA,HP⟩:=exists_identity_extension hn ht ha hR0 old hv (by omega)
    obtain ⟨q,hq,HDepth,HDim',HC',HPath,HP'⟩:=ih next hNext (by rw [HDim,HD];omega)
    refine ⟨q,hq,by omega,HDim'.trans HDim,HC'.trans HC,?_,HP.trans HP'⟩
    exact (Relation.ReflTransGen.single HA).trans HPath

/-- Every accepted native vertex reaches a terminal-depth vertex at the same point. -/
theorem exists_terminal_identity_extension (old :List Bool) (hv :V old) :
    ∃q,∃hq :V q,
      IntegralMixedRoadmapAtomic.depth q=D q ∧
      IntegralMixedRoadmapAtomic.candidate q=IntegralMixedRoadmapAtomic.candidate old ∧
      Relation.ReflTransGen A old q ∧
      HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
        (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq):=by
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 old hv
  obtain ⟨q,hq,HDepth,HDim,HC,HPath,HP⟩:=exists_identity_extension_by hn ht ha hR0
    (D old-IntegralMixedRoadmapAtomic.depth old) old hv (by omega)
  exact ⟨q,hq,by omega,HC,HPath,HP⟩

theorem exists_terminal_raw_reachable (old :List Bool) (hv :V old) :
    ∃q,IntegralMixedRoadmapAtomic.depth q=D q ∧
      RawReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old q:=by
  obtain ⟨q,hq,HD,HC,HPath,_⟩:=exists_terminal_identity_extension hn ht ha hR0 old hv
  exact ⟨q,HD,hv,hq,rfl,HC,HPath⟩

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
