/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ComponentSlabCover
/-! # Overlapping slab anchors connect through the recursive endpoint fiber

All critical anchors may be retained as labels. Clopen transported pieces
that overlap agree, and their connected endpoint limit joins both branch
endpoints in a recursively covered fiber. No midpoint-component test is
needed for this implication.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ComponentSlabCover.InteriorData
open Set
open scoped Classical
variable {X J L R : Type*} [TopologicalSpace X] {p : X→ℝ} {a b : ℝ}
    (D : ComponentSlabCover.InteriorData p a b J)

theorem piece_eq_of_overlap (Hcl : ∀j,IsClopen (D.piece j)) {i j : J}
    (H : ClosedPathCover.Overlap D.piece i j) : D.piece i=D.piece j :=by
  obtain ⟨z,hzi,hzj⟩:=H
  have HI : IsPathConnected (D.piece i):=⟨z,hzi,fun y hy=>D.paths i z hzi y hy⟩
  have HJ : IsPathConnected (D.piece j):=⟨z,hzj,fun y hy=>D.paths j z hzj y hy⟩
  exact Subset.antisymm
    (HI.isConnected.isPreconnected.subset_isClopen (Hcl j) ⟨z,hzi,hzj⟩)
    (HJ.isConnected.isPreconnected.subset_isClopen (Hcl i) ⟨z,hzj,hzi⟩)

theorem left_endpoints_joined (Hcl : ∀j,IsClopen (D.piece j)) (hab : a<b)
    (left : ClopenPathCover (p ⁻¹' {a}) L) {i j : J}
    (H : ClosedPathCover.Overlap D.piece i j) :
    JoinedIn (p ⁻¹' {a}) (D.arc i a) (D.arc j a) :=by
  have HE : D.ambient j=D.ambient i:=by
    exact congrArg (fun s : Set (p ⁻¹' Ioo a b)=>Subtype.val '' s)
      (D.piece_eq_of_overlap Hcl H).symm
  have HI:=D.endpoint_mem_closure hab i (show a∈Icc a b from ⟨le_rfl,hab.le⟩)
  have HJ:=D.endpoint_mem_closure hab j (show a∈Icc a b from ⟨le_rfl,hab.le⟩)
  rw [HE] at HJ
  obtain ⟨l,hl⟩:=left.imagePiece_cover (D.arc i a) (D.level_left i)
  have Hkeep:=left.subset_imagePiece_of_isPreconnected (D.limit_left i) inter_subset_right
    ⟨HI,D.level_left i⟩ hl
  exact (left.imagePiece_paths l _ hl _ (Hkeep ⟨HJ,D.level_left j⟩)).mono (left.imagePiece_subset l)

theorem right_endpoints_joined (Hcl : ∀j,IsClopen (D.piece j)) (hab : a<b)
    (right : ClopenPathCover (p ⁻¹' {b}) R) {i j : J}
    (H : ClosedPathCover.Overlap D.piece i j) :
    JoinedIn (p ⁻¹' {b}) (D.arc i b) (D.arc j b) :=by
  have HE : D.ambient j=D.ambient i:=by
    exact congrArg (fun s : Set (p ⁻¹' Ioo a b)=>Subtype.val '' s)
      (D.piece_eq_of_overlap Hcl H).symm
  have HI:=D.endpoint_mem_closure hab i (show b∈Icc a b from ⟨hab.le,le_rfl⟩)
  have HJ:=D.endpoint_mem_closure hab j (show b∈Icc a b from ⟨hab.le,le_rfl⟩)
  rw [HE] at HJ
  obtain ⟨r,hr⟩:=right.imagePiece_cover (D.arc i b) (D.level_right i)
  have Hkeep:=right.subset_imagePiece_of_isPreconnected (D.limit_right i) inter_subset_right
    ⟨HI,D.level_right i⟩ hr
  exact (right.imagePiece_paths r _ hr _ (Hkeep ⟨HJ,D.level_right j⟩)).mono (right.imagePiece_subset r)

end LeanCanny.Connectivity.ComponentSlabCover.InteriorData
