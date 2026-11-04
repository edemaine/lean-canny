/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FiniteSlabCover
/-! # Finite slab paths with only actual cut-boundary intermediate points

Interior intersections in one slab remain a pending path. Changing slabs
flushes that path at their common cut, so no interior representative enters
the resulting endpoint walk.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FiniteSlabEndpointPaths
open Set
variable {X :Type*} [TopologicalSpace X] {n :ℕ}

/-- A point on one of the finitely many actual cut fibers. -/
def CutPoint (p :X→ℝ) (cut :ℕ→ℝ) (n :ℕ):= {x :X //∃i :Fin (n+2),p x=cut i.val}

/-- Both endpoints are boundary points of the same closed slab, and the
step is an actual path inside that slab. -/
def SlabStep (p :X→ℝ) (cut :ℕ→ℝ) (x y :CutPoint p cut n):Prop:=
  ∃i :Fin (n+1),(p x.val=cut i.val∨p x.val=cut (i.val+1)) ∧
    (p y.val=cut i.val∨p y.val=cut (i.val+1)) ∧
    JoinedIn (p ⁻¹' Icc (cut i.val) (cut (i.val+1))) x.val y.val

abbrev EndpointReach (p :X→ℝ) (cut :ℕ→ℝ):=
  Relation.ReflTransGen (SlabStep (n:=n) p cut)

omit [TopologicalSpace X] in
private theorem boundary_in_slab (p :X→ℝ) (cut :ℕ→ℝ)
    (hcut :StrictMonoOn cut (Icc 0 (n+1))) (i :Fin (n+1)) (x :CutPoint p cut n)
    (hx :p x.val∈Icc (cut i.val) (cut (i.val+1))):
    p x.val=cut i.val∨p x.val=cut (i.val+1):=by
  obtain ⟨j,hj⟩:=x.property
  have HI :i.val≤j.val:=by
    by_contra H
    have HL:=hcut ⟨Nat.zero_le _,by omega⟩ ⟨Nat.zero_le _,by omega⟩ (show j.val<i.val by omega)
    exact (not_lt_of_ge (hj ▸ hx.1)) HL
  have HJ :j.val≤i.val+1:=by
    by_contra H
    have HL:=hcut ⟨Nat.zero_le _,by omega⟩ ⟨Nat.zero_le _,by omega⟩ (show i.val+1<j.val by omega)
    exact (not_lt_of_ge (hj ▸ hx.2)) HL
  by_cases HE :j.val=i.val
  · exact Or.inl (hj.trans (congrArg cut HE))
  · have HE' :j.val=i.val+1:=by omega
    exact Or.inr (hj.trans (congrArg cut HE'))

/-- Global cut membership and a path in one strict slab already imply both
of that slab's exact endpoint conditions. -/
theorem slabStep_of_joinedIn (p :X→ℝ) (cut :ℕ→ℝ)
    (hcut :StrictMonoOn cut (Icc 0 (n+1))) (i :Fin (n+1)) {x y :CutPoint p cut n}
    (H :JoinedIn (p ⁻¹' Icc (cut i.val) (cut (i.val+1))) x.val y.val):SlabStep p cut x y:=
  ⟨i,boundary_in_slab p cut hcut i x H.source_mem,
    boundary_in_slab p cut hcut i y H.target_mem,H⟩

variable (p :X→ℝ) (cut :ℕ→ℝ) {J :Fin (n+1)→Type*}
  (C :∀i,ClopenPathCover (p ⁻¹' Icc (cut i.val) (cut (i.val+1))) (J i))

private theorem piece_path (v :Σi,J i) (x :X) (hx :x∈FiniteSlabCover.piece p cut C v)
    (y :X) (hy :y∈FiniteSlabCover.piece p cut C v):
    JoinedIn (p ⁻¹' Icc (cut v.1.val) (cut (v.1.val+1))) x y:=
  (FiniteSlabCover.paths p cut C v x hx y hy).mono (FiniteSlabCover.piece_subset p cut C v)

private theorem overlap_at_cut (hcut :StrictMonoOn cut (Icc 0 (n+1)))
    (v w :Σi,J i) (hne :v.1≠w.1)
    (x :X) (hv :x∈FiniteSlabCover.piece p cut C v) (hw :x∈FiniteSlabCover.piece p cut C w):
    ∃i :Fin (n+2),p x=cut i.val:=by
  have HI:=FiniteSlabCover.overlap_indices p cut C hcut (show
    ClosedPathCover.Overlap (FiniteSlabCover.piece p cut C) v w from ⟨x,hv,hw⟩)
  have HV:=FiniteSlabCover.piece_subset p cut C v hv
  have HW:=FiniteSlabCover.piece_subset p cut C w hw
  have Hne :v.1.val≠w.1.val:=fun H=>hne (Fin.ext H)
  rcases lt_or_gt_of_ne Hne with H|H
  · have HE :w.1.val=v.1.val+1:=by omega
    refine ⟨w.1.castSucc,le_antisymm ?_ HW.1⟩
    exact le_of_le_of_eq HV.2 (congrArg cut HE.symm)
  · have HE :v.1.val=w.1.val+1:=by omega
    refine ⟨v.1.castSucc,le_antisymm ?_ HV.1⟩
    exact le_of_le_of_eq HW.2 (congrArg cut HE.symm)

/-- The pending path stays in the current slab. Only a transition to a
DIFFERENT slab creates a new endpoint vertex. -/
private theorem reachable_pending (hcut :StrictMonoOn cut (Icc 0 (n+1)))
    {v w :Σi,J i} (H :Relation.ReflTransGen (ClosedPathCover.Overlap (FiniteSlabCover.piece p cut C)) v w)
    (x :CutPoint p cut n) (hx :x.val∈FiniteSlabCover.piece p cut C v):
    ∃z :CutPoint p cut n,EndpointReach p cut x z ∧
      ∀y∈FiniteSlabCover.piece p cut C w,
        JoinedIn (p ⁻¹' Icc (cut w.1.val) (cut (w.1.val+1))) z.val y:=by
  induction H with
  | refl=>exact ⟨x,.refl,fun y hy=>piece_path p cut C _ x.val hx y hy⟩
  | @tail v w H hedge ih=>
    obtain ⟨z,hz,hpending⟩:=ih
    obtain ⟨u,huv,huw⟩:=hedge
    by_cases HE :v.1=w.1
    · refine ⟨z,hz,?_⟩
      intro y hy
      have HP:=hpending u huv
      rw [HE] at HP
      exact HP.trans (piece_path p cut C w u huw y hy)
    · let boundary:CutPoint p cut n:=⟨u,overlap_at_cut p cut C hcut v w HE u huv huw⟩
      refine ⟨boundary,hz.tail (slabStep_of_joinedIn p cut hcut v.1 (hpending u huv)),?_⟩
      intro y hy
      exact piece_path p cut C w u huw y hy

/-- A finite boundary walk gives an actual ambient path, without finiteness,
closedness or any cover assumption. -/
theorem joinedIn_of_endpointReach {x y :CutPoint p cut n} (H :EndpointReach p cut x y):
    JoinedIn univ x.val y.val:=by
  induction H with
  | refl=>exact JoinedIn.refl (mem_univ _)
  | tail H hedge ih=>
    obtain ⟨i,hx,hy,hpath⟩:=hedge
    exact ih.trans (hpath.mono (subset_univ _))

variable [∀i,Finite (J i)]

include C in
/-- Every ambient path between actual cut points is a finite walk of paths
in individual closed slabs, with EVERY intermediate point on an actual cut.
Same-slab interior overlaps are composed before a boundary step is emitted. -/
theorem endpointReach_of_joinedIn (hp :Continuous p)
    (hcut :StrictMonoOn cut (Icc 0 (n+1)))
    (hbound :∀x,p x∈Icc (cut 0) (cut (n+1)))
    {x y :CutPoint p cut n} (H :JoinedIn univ x.val y.val):EndpointReach p cut x y:=by
  obtain ⟨v,hv⟩:=FiniteSlabCover.cover p cut C hbound x.val
  obtain ⟨w,hw⟩:=FiniteSlabCover.cover p cut C hbound y.val
  have HR:=(FiniteSlabCover.joinedIn_iff_reachable p cut C hp hbound hv hw).mp H
  obtain ⟨z,hz,hpending⟩:=reachable_pending p cut C hcut HR x hv
  exact hz.tail (slabStep_of_joinedIn p cut hcut w.1 (hpending y.val hw))

include C in
theorem joinedIn_iff_endpointReach (hp :Continuous p)
    (hcut :StrictMonoOn cut (Icc 0 (n+1)))
    (hbound :∀x,p x∈Icc (cut 0) (cut (n+1))) (x y :CutPoint p cut n):
    JoinedIn univ x.val y.val↔EndpointReach p cut x y:=
  ⟨endpointReach_of_joinedIn p cut C hp hcut hbound,joinedIn_of_endpointReach p cut⟩

end LeanCanny.Connectivity.FiniteSlabEndpointPaths
