/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ClopenPathCover

/-! # Assembling all the closed slabs of a finite sweep

The component covers constructed for individual closed slabs can be assembled
into a cover of the original space. The construction retains the slab and
recursive piece labels, and saturates their finite overlap graph. Adjacent
slabs communicate only through their common endpoint fiber. Strictly separated
slabs have no overlap edge.

Repeated cut values are allowed: their degenerate slabs need only a cover of
the corresponding fiber. This construction does not supply the recursive
slice covers or an effective writer for their membership predicates.
-/

@[expose] public section

namespace LeanCanny.Connectivity.FiniteSlabCover
open Set

/-- Every point between the first and last cut belongs to an adjacent closed
interval. This includes repeated cuts and needs no monotonicity assumption. -/
theorem exists_adjacent_interval (cut : ℕ → ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (cut 0) (cut (n + 1))) :
    ∃ i : Fin (n + 1), x ∈ Icc (cut i.val) (cut (i.val + 1)) := by
  induction n with
  | zero => exact ⟨0, hx⟩
  | succ n ih =>
    by_cases h : x ≤ cut (n + 1)
    · obtain ⟨i, hi⟩ := ih ⟨hx.1, h⟩
      exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last (n + 1), le_of_lt (lt_of_not_ge h), hx.2⟩

variable {X : Type*} [TopologicalSpace X] {n : ℕ}
  (p : X → ℝ) (cut : ℕ → ℝ) {J : Fin (n + 1) → Type*}
  (C : ∀ i, ClopenPathCover (p ⁻¹' Icc (cut i.val) (cut (i.val + 1))) (J i))

/-- The actual ambient pieces, with both the slab and its recursive label
retained. No new point or path choice occurs in this definition. -/
def piece (v : Σ i, J i) : Set X := (C v.1).imagePiece v.2

theorem piece_subset (v : Σ i, J i) :
    piece p cut C v ⊆ p ⁻¹' Icc (cut v.1.val) (cut (v.1.val + 1)) :=
  (C v.1).imagePiece_subset v.2

theorem closed (hp : Continuous p) (v : Σ i, J i) : IsClosed (piece p cut C v) :=
  (C v.1).imagePiece_closed (isClosed_Icc.preimage hp) v.2

theorem cover (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1))) :
    ∀ x, ∃ v, x ∈ piece p cut C v := by
  intro x
  obtain ⟨i, hi⟩ := exists_adjacent_interval cut n (hbound x)
  obtain ⟨j, hj⟩ := (C i).imagePiece_cover x hi
  exact ⟨⟨i, j⟩, hj⟩

theorem paths (v : Σ i, J i) (x : X) (hx : x ∈ piece p cut C v)
    (y : X) (hy : y ∈ piece p cut C v) : JoinedIn (piece p cut C v) x y :=
  (C v.1).imagePiece_paths v.2 x hx y hy

/-- An overlap in one slab is exactly the original recursive cover's overlap;
passing to the original ambient space creates no new edges. -/
theorem overlap_same_slab_iff (i : Fin (n + 1)) (j k : J i) :
    ClosedPathCover.Overlap (piece p cut C) ⟨i, j⟩ ⟨i, k⟩ ↔
      ClosedPathCover.Overlap (C i).piece j k := by
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, z, hz, he⟩
    have : z = y := Subtype.ext he
    subst z
    exact ⟨y, hy, hz⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x.val, ⟨x, hx, rfl⟩, x, hy, rfl⟩

/-- Two slabs with a common boundary value can intersect only in that fiber.
The converse uses the same point, so this is an exact endpoint attachment test. -/
theorem overlap_touching_iff (i j : Fin (n + 1))
    (hcut : cut (i.val + 1) = cut j.val) (u : J i) (v : J j) :
    ClosedPathCover.Overlap (piece p cut C) ⟨i, u⟩ ⟨j, v⟩ ↔
      ∃ z : p ⁻¹' {cut (i.val + 1)},
        z.val ∈ piece p cut C ⟨i, u⟩ ∧ z.val ∈ piece p cut C ⟨j, v⟩ := by
  constructor
  · rintro ⟨x, hx, hy⟩
    have hxi := piece_subset p cut C ⟨i, u⟩ hx
    have hxj := piece_subset p cut C ⟨j, v⟩ hy
    have he : p x = cut (i.val + 1) := le_antisymm hxi.2 (hcut ▸ hxj.1)
    exact ⟨⟨x, he⟩, hx, hy⟩
  · rintro ⟨z, hx, hy⟩
    exact ⟨z.val, hx, hy⟩

/-- Consecutive slabs attach through the actual recursive exceptional fiber. -/
theorem overlap_adjacent_iff (i : Fin n) (u : J i.castSucc) (v : J i.succ) :
    ClosedPathCover.Overlap (piece p cut C) ⟨i.castSucc, u⟩ ⟨i.succ, v⟩ ↔
      ∃ z : p ⁻¹' {cut (i.val + 1)},
        z.val ∈ piece p cut C ⟨i.castSucc, u⟩ ∧
          z.val ∈ piece p cut C ⟨i.succ, v⟩ :=
  overlap_touching_iff p cut C i.castSucc i.succ rfl u v

theorem not_overlap_of_separated (i j : Fin (n + 1))
    (hcut : cut (i.val + 1) < cut j.val) (u : J i) (v : J j) :
    ¬ ClosedPathCover.Overlap (piece p cut C) ⟨i, u⟩ ⟨j, v⟩ := by
  rintro ⟨x, hx, hy⟩
  have hxi := piece_subset p cut C ⟨i, u⟩ hx
  have hxj := piece_subset p cut C ⟨j, v⟩ hy
  exact (not_lt_of_ge (hxj.1.trans hxi.2)) hcut

theorem not_overlap_of_nonadjacent (hcut : StrictMonoOn cut (Icc 0 (n + 1)))
    (i j : Fin (n + 1))
    (hij : i.val + 1 < j.val) (u : J i) (v : J j) :
    ¬ ClosedPathCover.Overlap (piece p cut C) ⟨i, u⟩ ⟨j, v⟩ :=
  not_overlap_of_separated p cut C i j
    (hcut ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩
      ⟨Nat.zero_le _, Nat.le_of_lt j.isLt⟩ hij) u v

/-- With strictly ordered cuts, every graph edge stays within a slab or moves
to a neighboring slab. Endpoint tests therefore account for all cross edges. -/
theorem overlap_indices (hcut : StrictMonoOn cut (Icc 0 (n + 1)))
    {i j : Fin (n + 1)}
    {u : J i} {v : J j}
    (h : ClosedPathCover.Overlap (piece p cut C) ⟨i, u⟩ ⟨j, v⟩) :
    j.val ≤ i.val + 1 ∧ i.val ≤ j.val + 1 := by
  constructor
  · by_contra hij
    exact not_overlap_of_nonadjacent p cut C hcut i j (lt_of_not_ge hij) u v h
  · by_contra hij
    apply not_overlap_of_nonadjacent p cut C hcut j i (lt_of_not_ge hij) v u
    obtain ⟨x, hx, hy⟩ := h
    exact ⟨x, hy, hx⟩

variable [∀ i, Finite (J i)]

/-- Saturating the assembled closed pieces produces the global recursive
component cover. The label type is the finite disjoint union of slab labels. -/
def componentCover (hp : Continuous p)
    (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1))) :
    ClopenPathCover X (Σ i, J i) :=
  ClopenPathCover.ofClosed (piece p cut C) (closed p cut C hp)
    (cover p cut C hbound) (paths p cut C)

/-- Saturated membership needs only the ordinary overlap graph and an original
slab membership query. There is no closure or global-component oracle in it. -/
theorem mem_componentCover_iff (hp : Continuous p)
    (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1))) (i : Σ k, J k) (x : X) :
    x ∈ (componentCover p cut C hp hbound).piece i ↔
      ∃ j, Relation.ReflTransGen (ClosedPathCover.Overlap (piece p cut C)) i j ∧
        x ∈ piece p cut C j := by
  have heq : FrontierCover.Incident (piece p cut C) =
      ClosedPathCover.Overlap (piece p cut C) := by
    funext i j
    apply propext
    simp only [FrontierCover.Incident, (closed p cut C hp i).closure_eq,
      (closed p cut C hp j).closure_eq, ClosedPathCover.Overlap,
      inter_comm (piece p cut C j) (piece p cut C i), or_self]
  change (∃ j, Relation.ReflTransGen (FrontierCover.Incident (piece p cut C)) i j ∧
    x ∈ piece p cut C j) ↔ _
  rw [heq]

/-- Empty recursive labels stay empty after saturation, so their original
validity predicates can be retained by a global graph implementation. -/
theorem componentCover_nonempty_iff (hp : Continuous p)
    (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1))) (i : Σ k, J k) :
    ((componentCover p cut C hp hbound).piece i).Nonempty ↔
      (piece p cut C i).Nonempty :=
  FrontierCover.component_nonempty_iff (piece p cut C) i

/-- Global paths may cross several slabs and exceptional fibers. Their exact
finite witness is a walk in the assembled overlap graph. -/
theorem joinedIn_iff_reachable (hp : Continuous p)
    (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1)))
    {i j : Σ k, J k} {x y : X}
    (hx : x ∈ piece p cut C i) (hy : y ∈ piece p cut C j) :
    JoinedIn univ x y ↔
      Relation.ReflTransGen (ClosedPathCover.Overlap (piece p cut C)) i j :=
  ClosedPathCover.joinedIn_iff_reachable (piece p cut C) (closed p cut C hp)
    (cover p cut C hbound) (paths p cut C) hx hy

theorem isPreconnected_iff_reachable (hp : Continuous p)
    (hbound : ∀ x, p x ∈ Icc (cut 0) (cut (n + 1))) :
    IsPreconnected (univ : Set X) ↔
      ∀ i j, (piece p cut C i).Nonempty → (piece p cut C j).Nonempty →
        Relation.ReflTransGen (ClosedPathCover.Overlap (piece p cut C)) i j :=
  ClosedPathCover.isPreconnected_iff_reachable (piece p cut C) (closed p cut C hp)
    (cover p cut C hbound) (paths p cut C)

end LeanCanny.Connectivity.FiniteSlabCover
