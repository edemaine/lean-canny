/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.OrderedRealCells
public import LeanCanny.Connectivity.AccessibleArc

/-! # Accessible covers by ordered real cells

Every gap admits a straight path from any closure point to any interior
point. Restriction to a set whose membership is constant on each cell gives
a finite accessible cover of that actual set. Excluded endpoints remain
excluded because all frontier closures are relative to the subtype.
-/

@[expose] public section
namespace LeanCanny.Connectivity.OrderedRealCellCover
open Set Geometry.OrderedRealCells
open scoped Classical

theorem gap_accessible (s : Finset ℝ) (k : Fin (s.card + 1)) : FrontierCover.Accessible (gap s k) := by
  intro x hx y hy
  refine ⟨Path.ofLine (f := fun t : ℝ => (1 - t) * x + t * y)
    (by fun_prop) (by simp) (by simp), ?_⟩
  intro t
  change (1 - (t : ℝ)) * x + (t : ℝ) * y ∈ insert x (gap s k)
  by_cases ht : (t : ℝ) = 0
  · simp only [ht, sub_zero, one_mul, zero_mul, add_zero, mem_insert_iff, true_or]
  · right
    have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    rw [mem_gap_iff]
    intro j
    have hyj := (mem_gap_iff s k y).mp hy j
    split_ifs with hj
    · rw [ite_eq_left hj] at hyj
      have hs : gap s k ⊆ Ici (root s j) := by
        intro z hz
        have H := (mem_gap_iff s k z).mp hz j
        rw [ite_eq_left hj] at H
        exact H.le
      have hxj : root s j ≤ x := (closure_minimal hs isClosed_Ici) hx
      nlinarith
    · rw [ite_eq_right hj] at hyj
      have hs : gap s k ⊆ Iic (root s j) := by
        intro z hz
        have H := (mem_gap_iff s k z).mp hz j
        rw [ite_eq_right hj] at H
        exact H.le
      have hxj : x ≤ root s j := (closure_minimal hs isClosed_Iic) hx
      nlinarith

theorem piece_accessible (s : Finset ℝ) (i : Index s) : FrontierCover.Accessible (piece s i) := by
  cases i with
  | inl i => exact FrontierCover.accessible_singleton _
  | inr k => exact gap_accessible s k

def Stable (s : Finset ℝ) (S : Set ℝ) : Prop :=
  ∀ i : Index s, ∀ x ∈ piece s i, ∀ y ∈ piece s i, x ∈ S ↔ y ∈ S

noncomputable def restrictedPiece (s : Finset ℝ) (S : Set ℝ) (i : Index s) : Set S :=
  ((↑) : S → ℝ) ⁻¹' piece s i

theorem restricted_cover (s : Finset ℝ) (S : Set ℝ) (x : S) :
    ∃ i : Index s, x ∈ restrictedPiece s S i := cover s x.val

theorem restricted_accessible (s : Finset ℝ) (S : Set ℝ) (hS : Stable s S) (i : Index s) :
    FrontierCover.Accessible (restrictedPiece s S i) := by
  by_cases hs : piece s i ⊆ S
  · exact (piece_accessible s i).subtype hs
  · have he : restrictedPiece s S i = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hs
      intro y hy
      exact (hS i x.val hx y hy).mp x.property
    rw [he]
    intro x hx
    simp only [closure_empty, mem_empty_iff_false] at hx

theorem joinedIn_iff_graph (s : Finset ℝ) (S : Set ℝ) (hS : Stable s S)
    {i j : Index s} {x y : S} (hx : x ∈ restrictedPiece s S i) (hy : y ∈ restrictedPiece s S j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (FrontierCover.Incident (restrictedPiece s S)) i j :=
  FrontierCover.joinedIn_iff_reachable (restrictedPiece s S) (restricted_cover s S)
    (restricted_accessible s S hS) hx hy

theorem preconnected_iff_graph (s : Finset ℝ) (S : Set ℝ) (hS : Stable s S) :
    IsPreconnected (univ : Set S) ↔ ∀ i j : Index s,
      (restrictedPiece s S i).Nonempty → (restrictedPiece s S j).Nonempty →
        Relation.ReflTransGen (FrontierCover.Incident (restrictedPiece s S)) i j :=
  FrontierCover.isPreconnected_iff_reachable (restrictedPiece s S) (restricted_cover s S)
    (restricted_accessible s S hS)

end LeanCanny.Connectivity.OrderedRealCellCover
