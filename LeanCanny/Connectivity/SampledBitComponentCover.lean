/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FiniteClopenWitness
public import LeanCanny.Geometry.CompleteConnectedIsometricPath
public import LeanCanny.Connectivity.BitPathCover
public import LeanCanny.Connectivity.ClopenPathCover

/-! # Bounded sample labels give actual component covers

A finite fixed-width family meeting every nonempty clopen piece already
indexes all actual components. Invalid words denote empty pieces. Completeness,
local connectedness and an isometric real embedding construct their paths.
The edge relation is explicitly SAME-component membership; no native cost
for that relation is inferred from the sample or label bounds.
-/
@[expose] public section
namespace LeanCanny.Connectivity.SampledBitComponentCover
open Set LeanCanny.Geometry
open scoped Classical
variable {X : Type*} [MetricSpace X] {w : ℕ}

structure Samples (X : Type*) [TopologicalSpace X] (w : ℕ) where
  good : List Bool→Prop
  point : {i : Vertex w // good i.val}→X
  hit : ∀ C : Set X,IsClopen C→C.Nonempty→∃ i,point i∈C

noncomputable def piece (A : Samples X w) (i : Vertex w) : Set X :=
  if h : A.good i.val then connectedComponent (A.point ⟨i,h⟩) else ∅

theorem piece_of_good (A : Samples X w) (i : Vertex w) (hi : A.good i.val) :
    piece A i=connectedComponent (A.point ⟨i,hi⟩) := dite_eq_left hi

theorem piece_of_not_good (A : Samples X w) (i : Vertex w) (hi : ¬A.good i.val) :
    piece A i=∅ := dite_eq_right hi

theorem components_finite (A : Samples X w) : Finite (ConnectedComponents X) :=
  FiniteClopenWitness.components_finite (range A.point) (finite_range A.point)
    (by intro C hC hN; obtain ⟨i,hi⟩:=A.hit C hC hN; exact ⟨A.point i,mem_range_self i,hi⟩)

theorem component_surjective (A : Samples X w) :
    Function.Surjective (fun i : {i : Vertex w // A.good i.val}=>ConnectedComponents.mk (A.point i)) := by
  let : Finite (ConnectedComponents X) := components_finite A
  intro c
  obtain ⟨x,rfl⟩:=ConnectedComponents.surjective_coe c
  obtain ⟨i,hi⟩:=A.hit (connectedComponent x) (FiniteComponentCover.isClopen_component x) ⟨x,mem_connectedComponent⟩
  exact ⟨i,ConnectedComponents.coe_eq_coe'.mpr hi⟩

theorem piece_clopen (A : Samples X w) (i : Vertex w) : IsClopen (piece A i) := by
  let : Finite (ConnectedComponents X) := components_finite A
  unfold piece
  split_ifs
  · exact FiniteComponentCover.isClopen_component _
  · exact isClopen_empty

theorem cover (A : Samples X w) (x : X) : ∃ i,x∈piece A i := by
  let : Finite (ConnectedComponents X) := components_finite A
  obtain ⟨i,hi⟩:=A.hit (connectedComponent x) (FiniteComponentCover.isClopen_component x) ⟨x,mem_connectedComponent⟩
  refine ⟨i.val,?_⟩
  rw [piece_of_good A i.val i.property]
  rw [←connectedComponent_eq hi]
  exact mem_connectedComponent

theorem piece_nonempty (A : Samples X w) (i : Vertex w) : (piece A i).Nonempty↔A.good i.val := by
  by_cases hi : A.good i.val
  · rw [piece_of_good A i hi]
    exact ⟨fun _=>hi,fun _=>⟨_,mem_connectedComponent⟩⟩
  · rw [piece_of_not_good A i hi]
    exact iff_of_false Set.not_nonempty_empty hi

theorem vertex_card_le (w : ℕ) : Nat.card (Vertex w)≤2^w := by
  let E := (Cslib.BitString.enumList w).toFinset
  let f : Vertex w→E := fun v=>⟨v.val,by simpa only [E,List.mem_toFinset,Cslib.BitString.mem_enumList] using v.property⟩
  have HF : Function.Injective f := by intro i j hij; exact Subtype.ext (congrArg (fun z : E=>z.val) hij)
  have H:=Nat.card_le_card_of_injective f HF
  have HC : Nat.card E=E.card := by simp
  rw [HC] at H
  exact H.trans ((List.toFinset_card_le _).trans_eq (Cslib.BitString.length_enumList w))

theorem component_card_le (A : Samples X w) : Nat.card (ConnectedComponents X)≤2^w :=
  (Nat.card_le_card_of_surjective _ (component_surjective A)).trans
    ((Nat.card_le_card_of_injective (fun i : {i : Vertex w // A.good i.val}=>i.val) Subtype.val_injective).trans
      (vertex_card_le w))

theorem overlap_iff (A : Samples X w) (i j : Vertex w) :
    (piece A i∩piece A j).Nonempty ↔
      ∃ hi : A.good i.val,∃ hj : A.good j.val,
        A.point ⟨j,hj⟩∈connectedComponent (A.point ⟨i,hi⟩) := by
  constructor
  · rintro ⟨x,hx,hy⟩
    have hi:=(piece_nonempty A i).mp ⟨x,hx⟩
    have hj:=(piece_nonempty A j).mp ⟨x,hy⟩
    refine ⟨hi,hj,?_⟩
    rw [piece_of_good A i hi] at hx
    rw [piece_of_good A j hj] at hy
    have HE:=(connectedComponent_eq hx).trans (connectedComponent_eq hy).symm
    rw [HE]
    exact mem_connectedComponent
  · rintro ⟨hi,hj,h⟩
    rw [piece_of_good A i hi,piece_of_good A j hj]
    exact ⟨A.point ⟨j,hj⟩,h,mem_connectedComponent⟩

theorem incident_iff_overlap (A : Samples X w) (i j : Vertex w) :
    FrontierCover.Incident (piece A) i j↔(piece A i∩piece A j).Nonempty := by
  rw [FrontierCover.Incident,(piece_clopen A i).isClosed.closure_eq,(piece_clopen A j).isClosed.closure_eq]
  constructor
  · rintro (⟨x,hx,hy⟩|⟨x,hx,hy⟩)
    · exact ⟨x,hx,hy⟩
    · exact ⟨x,hy,hx⟩
  · intro h
    exact Or.inl h

theorem incident_iff (A : Samples X w) (i j : Vertex w) :
    FrontierCover.Incident (piece A) i j↔
      ∃ hi : A.good i.val,∃ hj : A.good j.val,
        A.point ⟨j,hj⟩∈connectedComponent (A.point ⟨i,hi⟩) :=
  (incident_iff_overlap A i j).trans (overlap_iff A i j)

section Paths
variable [CompleteSpace X] [LocallyConnectedSpace X]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem component_paths (A : Samples X w) (e : X→V) (he : Isometry e) (a : X)
    (x : X) (hx : x∈connectedComponent a) (y : X) (hy : y∈connectedComponent a) :
    JoinedIn (connectedComponent a) x y := by
  let : Finite (ConnectedComponents X) := components_finite A
  have HC:=FiniteComponentCover.isClopen_component a
  let : ConnectedSpace (connectedComponent a) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : CompleteSpace (connectedComponent a) := HC.isClosed.isComplete.completeSpace_coe
  let : LocallyConnectedSpace (connectedComponent a) := HC.isOpen.locallyConnectedSpace
  let f : connectedComponent a→V := fun z=>e z.val
  have HF : Isometry f := he.comp (Isometry.of_dist_eq (fun _ _=>rfl))
  exact (joinedIn_iff_joined hx hy).mpr (CompleteConnectedIsometricPath.joined f HF ⟨x,hx⟩ ⟨y,hy⟩)

noncomputable def clopenCover (A : Samples X w) (e : X→V) (he : Isometry e) : ClopenPathCover X (Vertex w) where
  piece := piece A
  clopen := piece_clopen A
  cover := cover A
  paths := by
    intro i x hx y hy
    by_cases hi : A.good i.val
    · rw [piece_of_good A i hi] at hx hy ⊢
      exact component_paths A e he _ x hx y hy
    · rw [piece_of_not_good A i hi] at hx
      exact False.elim (Set.not_nonempty_empty ⟨x,hx⟩)

theorem accessible (A : Samples X w) (e : X→V) (he : Isometry e) (i : Vertex w) :
    FrontierCover.Accessible (piece A i) := by
  intro x hx y hy
  have HX : x∈piece A i := (piece_clopen A i).isClosed.closure_eq ▸ hx
  exact ((clopenCover A e he).paths i x HX y hy).mono (subset_insert x _)
end Paths
end LeanCanny.Connectivity.SampledBitComponentCover
