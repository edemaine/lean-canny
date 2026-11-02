/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BitFrontierCover

/-! # Two reserved endpoint words in an accessible frontier cover

The original pieces receive prefix `00`; `01` and `10` followed by zero
padding name the two endpoints. Every other word denotes an empty piece.
No algorithm for frontier incidence is asserted by this construction.
-/
@[expose] public section
namespace LeanCanny.Connectivity.BitEndpointFrontier
open Set Computation
open scoped Classical

def source (w : ℕ) : List Bool := false::true::List.replicate w false
def target (w : ℕ) : List Bool := true::false::List.replicate w false
def original (u : List Bool) : List Bool := false::false::u
def IsOriginal (w : ℕ) (u : List Bool) : Prop :=
  (u.drop 2).length=w ∧ u.take 2=[false,false]

@[simp] theorem source_length (w : ℕ) : (source w).length=w+2 := by simp [source]
@[simp] theorem target_length (w : ℕ) : (target w).length=w+2 := by simp [target]
@[simp] theorem original_length (u : List Bool) : (original u).length=u.length+2 := by simp [original]
@[simp] theorem isOriginal_original (w : ℕ) (u : Vertex w) : IsOriginal w (original u.val) := by
  simp [IsOriginal,original,u.property]
@[simp] theorem not_isOriginal_source (w : ℕ) : ¬IsOriginal w (source w) := by simp [IsOriginal,source]
@[simp] theorem not_isOriginal_target (w : ℕ) : ¬IsOriginal w (target w) := by simp [IsOriginal,target]
@[simp] theorem source_ne_target (w : ℕ) : source w≠target w := by simp [source,target]

variable {X : Type*} [TopologicalSpace X] {w : ℕ}
  {edges : List Bool→List Bool→Bool} {valids : List Bool→Bool}

noncomputable def rawPiece (P : Vertex w→Set X) (S T : Set X) (u : List Bool) : Set X :=
  if h : IsOriginal w u then P ⟨u.drop 2,h.1⟩
  else if u=source w then S else if u=target w then T else ∅

noncomputable def piece (P : Vertex w→Set X) (S T : Set X) (u : Vertex (w+2)) : Set X :=
  rawPiece P S T u.val

noncomputable def valid (w : ℕ) (v : List Bool→Bool) (s t : Bool) (u : List Bool) : Bool :=
  if IsOriginal w u then v (u.drop 2)
  else if u=source w then s else if u=target w then t else false

noncomputable def edge (P : Vertex w→Set X) (S T : Set X) (u v : List Bool) : Bool :=
  if hu : u.length=w+2 then if hv : v.length=w+2 then
    decide (FrontierCover.Incident (piece P S T) ⟨u,hu⟩ ⟨v,hv⟩) else false else false

theorem rawPiece_original (C : BitFrontierCover X w edges valids) (S T : Set X) (u : Vertex w) :
    rawPiece C.piece S T (original u.val)=C.piece u := by
  simp only [rawPiece,dite_eq_left (isOriginal_original w u)]
  rfl

omit [TopologicalSpace X] in
@[simp] theorem rawPiece_source (P : Vertex w→Set X) (S T : Set X) :
    rawPiece P S T (source w)=S := by simp [rawPiece]
omit [TopologicalSpace X] in
@[simp] theorem rawPiece_target (P : Vertex w→Set X) (S T : Set X) :
    rawPiece P S T (target w)=T := by simp [rawPiece,Ne.symm (source_ne_target w)]

theorem accessible (C : BitFrontierCover X w edges valids) (S T : Set X)
    (hs : FrontierCover.Accessible S) (ht : FrontierCover.Accessible T) (u : Vertex (w+2)) :
    FrontierCover.Accessible (piece C.piece S T u) := by
  unfold piece rawPiece
  split_ifs with ho hs' ht'
  · exact C.accessible _
  · exact hs
  · exact ht
  · intro _ _ y hy
    exact False.elim (Set.not_nonempty_empty ⟨y,hy⟩)

noncomputable def cover (C : BitFrontierCover X w edges valids) (S T : Set X)
    (hs : FrontierCover.Accessible S) (ht : FrontierCover.Accessible T) :
    BitFrontierCover X (w+2) (edge C.piece S T) (valid w valids (decide S.Nonempty) (decide T.Nonempty)) where
  piece := piece C.piece S T
  cover x := by
    obtain ⟨u,hu⟩:=C.cover x
    refine ⟨⟨original u.val,by rw [original_length,u.property]⟩,?_⟩
    change x∈rawPiece C.piece S T (original u.val)
    rw [rawPiece_original]
    exact hu
  accessible := accessible C S T hs ht
  valid_iff u := by
    unfold valid piece rawPiece
    split_ifs with ho hs' ht'
    · exact C.valid_iff ⟨u.val.drop 2,ho.1⟩
    · simp only [decide_eq_true_eq]
    · simp only [decide_eq_true_eq]
    · exact iff_of_false id Set.not_nonempty_empty
  edge_iff u v := by
    simp only [edge,dite_eq_left u.property,dite_eq_left v.property,decide_eq_true_eq]

theorem joinedIn_iff (C : BitFrontierCover X w edges valids) (S T : Set X)
    (hs : FrontierCover.Accessible S) (ht : FrontierCover.Accessible T)
    {x y : X} (hx : x∈S) (hy : y∈T) :
    JoinedIn univ x y ↔
      ImplicitGraph.Reachable (edge C.piece S T)
        (valid w valids (decide S.Nonempty) (decide T.Nonempty)) (w+2) (source w) (target w) := by
  apply (cover C S T hs ht).joinedIn_iff_reachable (source_length w) (target_length w)
  · change x∈rawPiece C.piece S T (source w)
    rw [rawPiece_source]
    exact hx
  · change y∈rawPiece C.piece S T (target w)
    rw [rawPiece_target]
    exact hy

end LeanCanny.Connectivity.BitEndpointFrontier
