/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FiniteSlabCover
public import LeanCanny.Connectivity.BitFrontierCover
public import LeanCanny.Encoding.FiniteSlabGraph

/-! # Bounded bit covers for an assembled finite sweep

Local closed-slab bit covers and endpoint-fiber intersection tests construct
the global bit cover. A binary slab tag is prepended to each local word.
Unused slab tags denote empty pieces, and local invalid records remain empty.
The graph has only local edges and adjacent endpoint attachment edges.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FiniteSlabBitCover
open Set LeanCanny.Encoding
open FiniteSlabGraph

variable {X : Type*} [TopologicalSpace X] {n s w : ℕ}
  (p : X → ℝ) (cut : ℕ → ℝ)
  (localEdge : ℕ → List Bool → List Bool → Bool)
  (localValid : ℕ → List Bool → Bool)
  (C : ∀ i : Fin (n + 1), BitPathCover
    (p ⁻¹' Icc (cut i.val) (cut (i.val + 1))) w (localEdge i.val) (localValid i.val))

def imagePiece (i : Fin (n + 1)) (u : Vertex w) : Set X :=
  Subtype.val '' (C i).piece u

def localWord (u : Vertex (s + w)) : Vertex w :=
  ⟨payload s u.val, by simp [payload, u.property]⟩

def piece (u : Vertex (s + w)) : Set X :=
  if h : tag s u.val < n + 1 then
    imagePiece p cut localEdge localValid C ⟨tag s u.val, h⟩ (localWord u)
  else ∅

/-- Pack the finite disjoint union of actual slab labels into the fixed-width
vertex type. Unused bit strings are retained as invalid records. -/
def pack (s : ℕ) (v : Σ _ : Fin (n + 1), Vertex w) : Vertex (s + w) :=
  ⟨encode s v.1.val v.2.val, by simp [v.2.property]⟩

theorem pack_injective (hcap : n + 1 ≤ 2 ^ s) :
    Function.Injective (pack (n := n) (w := w) s) := by
  intro u v h
  have he := congrArg Subtype.val h
  obtain ⟨hi, hw⟩ := encode_injective (u.1.isLt.trans_le hcap)
    (v.1.isLt.trans_le hcap) he
  exact Sigma.ext (Fin.ext hi) (heq_of_eq (Subtype.ext hw))

theorem piece_of_tag (u : Vertex (s + w)) (i : Fin (n + 1))
    (hi : tag s u.val = i.val) :
    piece p cut localEdge localValid C u =
      imagePiece p cut localEdge localValid C i (localWord u) := by
  have h : tag s u.val < n + 1 := hi ▸ i.isLt
  rw [piece, dite_eq_left h]
  exact congrArg (fun k => imagePiece p cut localEdge localValid C k (localWord u))
    (Fin.ext hi)

theorem piece_pack (hcap : n + 1 ≤ 2 ^ s) (i : Fin (n + 1)) (u : Vertex w) :
    piece p cut localEdge localValid C (pack s ⟨i, u⟩) =
      imagePiece p cut localEdge localValid C i u := by
  rw [piece_of_tag p cut localEdge localValid C _ i
    (tag_encode s i.val u.val (i.isLt.trans_le hcap))]
  have hword : localWord (pack s ⟨i, u⟩) = u :=
    Subtype.ext (payload_encode s i.val u.val)
  rw [hword]

theorem piece_invalid (u : Vertex (s + w)) (hi : ¬ tag s u.val < n + 1) :
    piece p cut localEdge localValid C u = ∅ := by simp [piece, hi]

theorem imagePiece_subset (i : Fin (n + 1)) (u : Vertex w) :
    imagePiece p cut localEdge localValid C i u ⊆
      p ⁻¹' Icc (cut i.val) (cut (i.val + 1)) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem imagePiece_closed (hp : Continuous p) (i : Fin (n + 1)) (u : Vertex w) :
    IsClosed (imagePiece p cut localEdge localValid C i u) :=
  (isClosed_Icc.preimage hp).isClosedEmbedding_subtypeVal.isClosedMap _ ((C i).closed u)

theorem imagePiece_paths (i : Fin (n + 1)) (u : Vertex w)
    {x y : X} (hx : x ∈ imagePiece p cut localEdge localValid C i u)
    (hy : y ∈ imagePiece p cut localEdge localValid C i u) :
    JoinedIn (imagePiece p cut localEdge localValid C i u) x y := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact ((C i).paths u x hx y hy).map continuous_subtype_val.continuousOn

theorem imagePiece_nonempty_iff (i : Fin (n + 1)) (u : Vertex w) :
    (imagePiece p cut localEdge localValid C i u).Nonempty ↔ localValid i.val u.val = true := by
  rw [(C i).valid_iff]
  exact Set.image_nonempty

theorem overlap_same_iff (i : Fin (n + 1)) (u v : Vertex w) :
    (imagePiece p cut localEdge localValid C i u ∩
      imagePiece p cut localEdge localValid C i v).Nonempty ↔
        localEdge i.val u.val v.val = true := by
  rw [(C i).edge_iff]
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, z, hz, he⟩
    have : z = y := Subtype.ext he
    subst z
    exact ⟨y, hy, hz⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x.val, ⟨x, hx, rfl⟩, x, hy, rfl⟩

theorem overlap_touching_iff (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (u v : Vertex w) :
    (imagePiece p cut localEdge localValid C i u ∩
      imagePiece p cut localEdge localValid C j v).Nonempty ↔
        ∃ z : p ⁻¹' {cut (i.val + 1)},
          z.val ∈ imagePiece p cut localEdge localValid C i u ∧
          z.val ∈ imagePiece p cut localEdge localValid C j v := by
  constructor
  · rintro ⟨x, hx, hy⟩
    have hxi := imagePiece_subset p cut localEdge localValid C i u hx
    have hxj := imagePiece_subset p cut localEdge localValid C j v hy
    have he : p x = cut (i.val + 1) := le_antisymm hxi.2 (hij ▸ hxj.1)
    exact ⟨⟨x, he⟩, hx, hy⟩
  · rintro ⟨z, hx, hy⟩
    exact ⟨z.val, hx, hy⟩

theorem not_overlap_of_nonadjacent (hcut : StrictMonoOn cut (Icc 0 (n + 1)))
    (i j : Fin (n + 1)) (hij : i.val + 1 < j.val) (u v : Vertex w) :
    ¬ (imagePiece p cut localEdge localValid C i u ∩
      imagePiece p cut localEdge localValid C j v).Nonempty := by
  rintro ⟨x, hx, hy⟩
  have hxi := imagePiece_subset p cut localEdge localValid C i u hx
  have hxj := imagePiece_subset p cut localEdge localValid C j v hy
  exact (not_lt_of_ge (hxj.1.trans hxi.2))
    (hcut ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩
      ⟨Nat.zero_le _, Nat.le_of_lt j.isLt⟩ hij)

variable (touch : ℕ → List Bool → List Bool → Bool)
  (htouch : ∀ (i j : Fin (n + 1)), i.val + 1 = j.val → ∀ u v : Vertex w,
    touch i.val u.val v.val = true ↔
      ∃ z : p ⁻¹' {cut (i.val + 1)},
        z.val ∈ imagePiece p cut localEdge localValid C i u ∧
        z.val ∈ imagePiece p cut localEdge localValid C j v)

include htouch in
theorem edge_iff (hcut : StrictMonoOn cut (Icc 0 (n + 1)))
    (u v : Vertex (s + w)) :
    edge (n + 1) s localEdge touch u.val v.val = true ↔
      (piece p cut localEdge localValid C u ∩ piece p cut localEdge localValid C v).Nonempty := by
  by_cases hu : tag s u.val < n + 1
  · by_cases hv : tag s v.val < n + 1
    · let i : Fin (n + 1) := ⟨tag s u.val, hu⟩
      let j : Fin (n + 1) := ⟨tag s v.val, hv⟩
      rw [piece_of_tag p cut localEdge localValid C u i rfl,
        piece_of_tag p cut localEdge localValid C v j rfl]
      simp only [edge, hu, hv, ite_true]
      by_cases he : tag s u.val = tag s v.val
      · have hij : i = j := Fin.ext he
        rw [ite_eq_left he, ← hij]
        exact (overlap_same_iff p cut localEdge localValid C i (localWord u) (localWord v)).symm
      · simp only [he, ite_false]
        by_cases hij : tag s u.val + 1 = tag s v.val
        · simp only [hij, ite_true]
          exact (htouch i j hij (localWord u) (localWord v)).trans
            (overlap_touching_iff p cut localEdge localValid C i j hij
              (localWord u) (localWord v)).symm
        · simp only [hij, ite_false]
          by_cases hji : tag s v.val + 1 = tag s u.val
          · simp only [hji, ite_true]
            rw [inter_comm]
            exact (htouch j i hji (localWord v) (localWord u)).trans
              (overlap_touching_iff p cut localEdge localValid C j i hji
                (localWord v) (localWord u)).symm
          · simp only [hji, ite_false, Bool.false_eq_true, false_iff]
            rcases lt_or_gt_of_ne he with hlt | hgt
            · exact not_overlap_of_nonadjacent p cut localEdge localValid C hcut i j
                (by dsimp [i, j]; omega) _ _
            · rw [inter_comm]
              exact not_overlap_of_nonadjacent p cut localEdge localValid C hcut j i
                (by dsimp [i, j]; omega) _ _
    · simp [edge, hu, hv, piece_invalid p cut localEdge localValid C v hv]
  · simp [edge, hu, piece_invalid p cut localEdge localValid C u hu]

/-- Construct the actual bounded global cover. Its width is the tag width plus
the local recursive width; no table of all slabs or vertices is stored. -/
def bitCover (hp : Continuous p) (hcut : StrictMonoOn cut (Icc 0 (n + 1)))
    (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1))) (hcap : n + 1 ≤ 2 ^ s) :
    BitPathCover X (s + w) (edge (n + 1) s localEdge touch)
      (valid (n + 1) s localValid) where
  piece := piece p cut localEdge localValid C
  closed := by
    intro u
    unfold piece
    split
    · exact imagePiece_closed p cut localEdge localValid C hp _ _
    · exact isClosed_empty
  cover := by
    intro x
    obtain ⟨i, hi⟩ := FiniteSlabCover.exists_adjacent_interval cut n (hbound x)
    obtain ⟨v, hv⟩ := (C i).cover ⟨x, hi⟩
    let u : Vertex (s + w) := ⟨encode s i.val v.val, by simp [v.property]⟩
    have ht : tag s u.val = i.val := tag_encode s i.val v.val (i.isLt.trans_le hcap)
    refine ⟨u, ?_⟩
    rw [piece_of_tag p cut localEdge localValid C u i ht]
    have hw : localWord u = v := Subtype.ext (payload_encode s i.val v.val)
    rw [hw]
    exact ⟨⟨x, hi⟩, hv, rfl⟩
  paths := by
    intro u x hx y hy
    by_cases hu : tag s u.val < n + 1
    · rw [piece, dite_eq_left hu] at hx hy ⊢
      exact imagePiece_paths p cut localEdge localValid C _ _ hx hy
    · rw [piece, dite_eq_right hu] at hx
      exact False.elim hx
  valid_iff := by
    intro u
    unfold piece valid
    split
    · exact (imagePiece_nonempty_iff p cut localEdge localValid C
        ⟨tag s u.val, ‹tag s u.val < n + 1›⟩ (localWord u)).symm
    · simp
  edge_iff := edge_iff p cut localEdge localValid C touch htouch hcut

end LeanCanny.Connectivity.FiniteSlabBitCover
