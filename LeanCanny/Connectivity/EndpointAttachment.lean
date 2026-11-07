/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FrontierCover
public import LeanCanny.Geometry.ConnectedSlabLimit
public import LeanCanny.Connectivity.AccessibleArc

/-! # Attaching a slab component to a recursively covered endpoint fiber

All boundary limits of one transported component lie in a connected endpoint
limit. A finite accessible cover of the endpoint fiber turns this connection
into paths inside that fiber. One accessible branch then attaches every
boundary limit to the slab component. No regularity is imposed at the endpoint.
-/

@[expose] public section

namespace LeanCanny.Connectivity.EndpointAttachment
open Set Geometry

variable {X I : Type*} [TopologicalSpace X] [T2Space X]
  (p : X → ℝ) {a b : ℝ} {s : Set X}

section Slice
variable [Finite I] (piece : I → Set (p ⁻¹' {a}))
  (hcover : ∀ x, ∃ i, x ∈ piece i)
  (haccess : ∀ i, FrontierCover.Accessible (piece i))

include hcover in
omit [T2Space X] in
/-- A connected endpoint limit induces a walk in the actual recursive slice
graph. Accessibility is unnecessary for this direction. -/
theorem reachable_in_slice {L : Set X} (hL : IsPreconnected L) (hsub : L ⊆ p ⁻¹' {a})
    {x y : p ⁻¹' {a}} {i j : I} (hx : x.val ∈ L) (hy : y.val ∈ L)
    (hxi : x ∈ piece i) (hyj : y ∈ piece j) :
    Relation.ReflTransGen (FrontierCover.Incident piece) i j := by
  have himage : Subtype.val '' ((Subtype.val : p ⁻¹' {a} → X) ⁻¹' L) = L := by
    exact (Subtype.image_preimage_val _ _).trans (inter_eq_right.mpr hsub)
  have hc : IsPreconnected ((Subtype.val : p ⁻¹' {a} → X) ⁻¹' L) := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isPreconnected_image.mp
    rwa [himage]
  exact FrontierCover.reachable_of_isPreconnected piece hcover hc hxi hyj hx hy

include hcover haccess in
omit [T2Space X] in
/-- The recursive slice graph supplies a path between any two points in a
connected subset of the endpoint fiber, including a singular fiber. -/
theorem joinedIn_slice {L : Set X} (hL : IsPreconnected L) (hsub : L ⊆ p ⁻¹' {a})
    {x y : X} (hx : x ∈ L) (hy : y ∈ L) : JoinedIn (p ⁻¹' {a}) x y := by
  let x' : p ⁻¹' {a} := ⟨x, hsub hx⟩
  let y' : p ⁻¹' {a} := ⟨y, hsub hy⟩
  obtain ⟨i, hi⟩ := hcover x'
  obtain ⟨j, hj⟩ := hcover y'
  have hj : JoinedIn univ x' y' := FrontierCover.joinedIn_of_reachable piece haccess hi hj
    (reachable_in_slice p piece hcover hL hsub hx hy hi hj)
  exact hj.map continuous_subtype_val.continuousOn |>.mono
    (by rintro z ⟨w, _, rfl⟩; exact w.property)

include hcover haccess in
/-- A critical-branch endpoint and every boundary limit point are joined
inside the recursively covered endpoint fiber. -/
theorem joinedIn_endpoint (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (htails : ∀ c : Ioo a b, IsPreconnected (ConnectedSlabLimit.tail p (a := a) s c.val))
    {x z : X} (hx : x ∈ closure s) (hpx : p x = a)
    (hz : z ∈ closure s) (hpz : p z = a) : JoinedIn (p ⁻¹' {a}) x z :=
  joinedIn_slice p piece hcover haccess
    (ConnectedSlabLimit.isPreconnected_endpoint p hp hab hs htails) inter_subset_right
    ⟨hx, hpx⟩ ⟨hz, hpz⟩

include hcover in
theorem reachable_endpoint (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (htails : ∀ c : Ioo a b, IsPreconnected (ConnectedSlabLimit.tail p (a := a) s c.val))
    {x z : p ⁻¹' {a}} {i j : I} (hx : x.val ∈ closure s) (hz : z.val ∈ closure s)
    (hxi : x ∈ piece i) (hzj : z ∈ piece j) :
    Relation.ReflTransGen (FrontierCover.Incident piece) i j :=
  reachable_in_slice p piece hcover
    (ConnectedSlabLimit.isPreconnected_endpoint p hp hab hs htails) inter_subset_right
    ⟨hx, x.property⟩ ⟨hz, z.property⟩ hxi hzj

include hcover haccess in
/-- Only one accessible branch endpoint is needed to attach every limit
point to the full slab component. The slice path is included explicitly. -/
theorem joinedIn_union (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (htails : ∀ c : Ioo a b, IsPreconnected (ConnectedSlabLimit.tail p (a := a) s c.val))
    {x z y : X} (hx : x ∈ closure s) (hpx : p x = a)
    (hz : z ∈ closure s) (hpz : p z = a)
    (hbranch : JoinedIn (insert z s) z y) : JoinedIn (p ⁻¹' {a} ∪ s) x y := by
  apply ((joinedIn_endpoint p piece hcover haccess hp hab hs htails hx hpx hz hpz).mono
    subset_union_left).trans
  exact hbranch.mono (insert_subset (Or.inl hpz) subset_union_right)

include hcover haccess in
/-- A continuous critical branch extending to the endpoint supplies all the
access data. Every limit point joins it through the recursively covered slice. -/
theorem joinedIn_curve (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (htails : ∀ c : Ioo a b, IsPreconnected (ConnectedSlabLimit.tail p (a := a) s c.val))
    (curve : ℝ → X) (hc : ContinuousOn curve (Icc a b))
    (hlevel : p (curve a) = a) (hcurve : curve '' Ioo a b ⊆ s)
    {x : X} (hx : x ∈ closure s) (hpx : p x = a) (t : Ioo a b) :
    JoinedIn (p ⁻¹' {a} ∪ s) x (curve t.val) := by
  have ha : a ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩
  have hz : curve a ∈ closure (curve '' Ioo a b) :=
    ((hc a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self).mem_closure_image ha
  have hbranch := FrontierCover.accessible_open_arc hc (curve a) hz (curve t.val)
    ⟨t.val, t.property, rfl⟩
  exact joinedIn_union p piece hcover haccess hp hab hs htails hx hpx
    (closure_mono hcurve hz) hlevel (hbranch.mono (insert_subset_insert hcurve))

end Slice
end LeanCanny.Connectivity.EndpointAttachment
