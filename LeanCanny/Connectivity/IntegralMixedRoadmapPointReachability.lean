/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapPointGlue
public import LeanCanny.Connectivity.IntegralMixedRoadmapProperGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapEdgeSymmetry

/-! # Native reachability is independent of the accepted point representatives

Geometric finite walks can use points while each native endpoint keeps its
own full word. At a common point, the actual native identity edge joins the
two independently sampled histories.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

theorem raw_reachable_trans {c a b d :List Bool}
    (H :RawReachable hn ht ha hR0 c a b) (K :RawReachable hn ht ha hR0 c b d) :
    RawReachable hn ht ha hR0 c a d:=
  ⟨H.1,K.2.1,H.2.2.1,K.2.2.2.1,H.2.2.2.2.trans K.2.2.2.2⟩

theorem raw_reachable_symm {c a b :List Bool} (H :RawReachable hn ht ha hR0 c a b) :
    RawReachable hn ht ha hR0 c b a:=by
  let : Std.Symm (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) :=
    ⟨fun _ _ => IntegralMixedRoadmapEdge.symm hn ht ha hR0⟩
  exact ⟨H.2.1,H.1,H.2.2.2.1,H.2.2.1,symm H.2.2.2.2⟩

/-- Actual native paths between accepted representatives of two entire points. -/
noncomputable def PointReachable (c :List Bool)
    (x y :Fin (n (pairFst c)+3+1)→ℝ) :Prop:=
  ∃a b, ∃(hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a),
    ∃(hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b),
    ∃(hc :IntegralMixedRoadmapAtomic.candidate a=c), ∃(hd :IntegralMixedRoadmapAtomic.candidate b=c),
    pointAt hn ht ha hR0 c a hA hc=x ∧ pointAt hn ht ha hR0 c b hB hd=y ∧
      RawReachable hn ht ha hR0 c a b

theorem point_reachable_of_raw {c a b :List Bool}
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (H :RawReachable hn ht ha hR0 c a b) :
    PointReachable hn ht ha hR0 c (pointAt hn ht ha hR0 c a hA hc)
      (pointAt hn ht ha hR0 c b hB hd):=
  ⟨a,b,hA,hB,hc,hd,rfl,rfl,H⟩

/-- The existential endpoint histories can be replaced by any accepted histories
at the same two points. No equality of words or roots is required. -/
theorem point_reachable_iff_raw (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c) :
    PointReachable hn ht ha hR0 c (pointAt hn ht ha hR0 c a hA hc)
      (pointAt hn ht ha hR0 c b hB hd) ↔ RawReachable hn ht ha hR0 c a b:=by
  constructor
  · rintro ⟨a',b',hA',hB',hc',hd',HA,HB,H⟩
    have HL:=raw_reachable_of_pointAt_eq hn ht ha hR0 c a a' hA hA' hc hc' HA.symm
    have HR:=raw_reachable_of_pointAt_eq hn ht ha hR0 c b' b hB' hB hd' hd HB
    exact raw_reachable_trans hn ht ha hR0 (raw_reachable_trans hn ht ha hR0 HL H) HR
  · exact point_reachable_of_raw hn ht ha hR0 hA hB hc hd

theorem PointReachable.trans {c :List Bool} {x y z :Fin (n (pairFst c)+3+1)→ℝ}
    (H :PointReachable hn ht ha hR0 c x y) (K :PointReachable hn ht ha hR0 c y z) :
    PointReachable hn ht ha hR0 c x z:=by
  obtain ⟨a,b,hA,hB,hc,hd,HA,HB,HP⟩:=H
  obtain ⟨b',d,hB',hD,hd',he,HB',HD,KP⟩:=K
  have HG:=raw_reachable_of_pointAt_eq hn ht ha hR0 c b b' hB hB' hd hd' (HB.trans HB'.symm)
  exact ⟨a,d,hA,hD,hc,he,HA,HD,
    raw_reachable_trans hn ht ha hR0 (raw_reachable_trans hn ht ha hR0 HP HG) KP⟩

theorem PointReachable.symm {c :List Bool} {x y :Fin (n (pairFst c)+3+1)→ℝ}
    (H :PointReachable hn ht ha hR0 c x y) :PointReachable hn ht ha hR0 c y x:=by
  obtain ⟨a,b,hA,hB,hc,hd,HA,HB,HP⟩:=H
  exact ⟨b,a,hB,hA,hd,hc,HB,HA,raw_reachable_symm hn ht ha hR0 HP⟩

/-- Every point path represented here is still a path in the actual original
regular zero set; no completeness assumption is used. -/
theorem PointReachable.joined {c :List Bool} {x y :Fin (n (pairFst c)+3+1)→ℝ}
    (H :PointReachable hn ht ha hR0 c x y) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c) x y:=by
  obtain ⟨a,b,hA,hB,hc,hd,HA,HB,HP⟩:=H
  simpa only [HA,HB] using raw_reachable_joined hn ht ha hR0 c a b HP

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
