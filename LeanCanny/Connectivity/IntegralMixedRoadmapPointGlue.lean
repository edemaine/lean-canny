/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry

/-! # Equal actual points glue independent accepted roadmap histories

The common original source fixes the point type. Native signature comparisons
and fixed-width vertex bounds are derived from each history's own acceptance.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapIdentity.point pointAt

private theorem glue_cast_heq {a b :ℕ} (h :a=b) (p :Fin a→ℝ) :
    HEq p (fun i :Fin b=>p (Fin.cast h.symm i)):=by
  cases h
  rfl

private theorem identity_pointAt_heq (c q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c) :
    HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv) (pointAt hn ht ha hR0 c q hv hc):=by
  have HI :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv):=by
    unfold IntegralMixedRoadmapIdentity.point
    exact glue_cast_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)) _
  have HP :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) (pointAt hn ht ha hR0 c q hv hc):=by
    unfold pointAt
    exact glue_cast_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 c q hc)) _
  exact HI.symm.trans HP

/-- Equality is tested on the entire physical point, with the full words
remaining at their independent roots. -/
theorem identity_language_iff_pointAt_eq (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c) :
    pair a b∈IntegralMixedRoadmapIdentity.language hn ht ha hR0 ↔
      pointAt hn ht ha hR0 c a hA hc=pointAt hn ht ha hR0 c b hB hd:=by
  constructor
  · exact identity_pointAt_eq hn ht ha hR0 c a b hA hB hc hd
  · intro HP
    apply (IntegralMixedRoadmapIdentity.language_iff hn ht ha hR0 a b hA hB (hc.trans hd.symm)).mpr
    exact (identity_pointAt_heq hn ht ha hR0 c a hA hc).trans
      ((heq_of_eq HP).trans (identity_pointAt_heq hn ht ha hR0 c b hB hd).symm)

theorem raw_reachable_of_pointAt_eq (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (HP :pointAt hn ht ha hR0 c a hA hc=pointAt hn ht ha hR0 c b hB hd) :
    RawReachable hn ht ha hR0 c a b:=by
  have HI:=(identity_language_iff_pointAt_eq hn ht ha hR0 c a b hA hB hc hd).mpr HP
  have HE :IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 a b:=Or.inl HI
  exact ⟨hA,hB,hc,hd,Relation.ReflTransGen.single HE⟩

/-- The bounded implicit graph uses the actual native encodings; no byte or
label-length premise is supplied. -/
theorem label_reachable_of_pointAt_eq (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (HP :pointAt hn ht ha hR0 c a hA hc=pointAt hn ht ha hR0 c b hB hd) :
    ImplicitGraph.Reachable (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c) (width hn ht ha hR0 c)
      (label hn ht ha hR0 c a) (label hn ht ha hR0 c b):=
  (label_reachable_iff hn ht ha hR0 c a b).mpr (raw_reachable_of_pointAt_eq hn ht ha hR0 c a b hA hB hc hd HP)

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
