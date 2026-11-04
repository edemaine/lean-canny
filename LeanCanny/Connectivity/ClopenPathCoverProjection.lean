/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClopenPathCoverRetract
/-! # Component-preserving closed projections retain each saturated label -/
@[expose] public section
namespace LeanCanny.Connectivity.ClopenPathCover
open Set
variable {X Y I :Type*} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace Y] in
/-- Every point of a projection fiber stays in the same clopen path piece. -/
theorem mem_image_iff_of_fiber_joined (C :ClopenPathCover X I) (p :X→Y)
    (hf :∀x z,p x=p z→JoinedIn univ x z) (i :I) (z :X):
    p z∈p '' C.piece i ↔z∈C.piece i:=by
  constructor
  · rintro ⟨x,hx,he⟩
    exact C.mem_of_joined i hx (hf x z he)
  · intro hz
    exact ⟨z,hz,rfl⟩

/-- The ACTUAL frontier-graph saturation of these images changes no label.
This also preserves empty records; no representatives are discarded. -/
theorem saturated_image_eq (C :ClopenPathCover X I) (p :X→Y) (hp :IsClosedMap p)
    (hf :∀x z,p x=p z→JoinedIn univ x z) (i :I):
    FrontierCover.component (fun j=>p '' C.piece j) i=p '' C.piece i:=by
  have HC (j :I):IsClosed (p '' C.piece j):=hp _ (C.clopen j).isClosed
  have HI {j k :I} (h :FrontierCover.Incident (fun a=>p '' C.piece a) j k):
      p '' C.piece k⊆p '' C.piece j:=by
    rw [FrontierCover.Incident,(HC j).closure_eq,(HC k).closure_eq] at h
    have HN:(p '' C.piece j∩p '' C.piece k).Nonempty:=by
      rcases h with ⟨y,hj,hk⟩|⟨y,hk,hj⟩
      · exact ⟨y,hj,hk⟩
      · exact ⟨y,hj,hk⟩
    obtain ⟨y,⟨x,hx,Hx⟩,⟨z,hz,Hz⟩⟩:=HN
    have HZ:z∈C.piece j:=C.mem_of_joined j hx (hf x z (Hx.trans Hz.symm))
    rintro t ⟨w,hw,rfl⟩
    exact ⟨w,C.mem_of_joined j HZ ((C.paths k z hz w hw).mono (subset_univ _)),rfl⟩
  have HW {j k :I} (h :Relation.ReflTransGen (FrontierCover.Incident (fun a=>p '' C.piece a)) j k):
      p '' C.piece k⊆p '' C.piece j:=by
    induction h with
    | refl=>exact subset_rfl
    | tail _ HE IH=>exact (HI HE).trans IH
  ext y
  constructor
  · rintro ⟨j,hj,hy⟩
    exact HW hj hy
  · intro hy
    exact ⟨i,Relation.ReflTransGen.refl,hy⟩

end LeanCanny.Connectivity.ClopenPathCover
