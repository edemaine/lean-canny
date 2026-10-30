/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineEndpointIncidence
public import LeanCanny.Encoding.FlatAffineEndpointCells
public import LeanCanny.Geometry.OrderedRealCellNeighborhood

/-! # Refined adjacent cells identify original slab endpoint edges

Only the gap next to an original endpoint is needed to determine incidence.
Extra midpoint roots can split an original slab without changing its endpoint
edges. Samples in the adjacent gap, still inside the original slab, exist and
identify precisely those original edges. Computing their algebraic signs
remains a separate native obligation.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointCellIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem left_iff {J : Type*} [Finite J] (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (i : Fin (FlatAffineEndpointCells.roots F hcone height r).card) {b : ℝ}
    (ha : SymbolicScaledSquarefree.scalarEvaluation (root (FlatAffineEndpointCells.roots F hcone height r) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (curve : J → ℝ → Fin (count F (pairFst r)) → ℝ)
    (hc : ∀ j, ContinuousOn (curve j) (Icc (root (FlatAffineEndpointCells.roots F hcone height r) i) b))
    (hroot : ∀ j t, t ∈ Icc (root (FlatAffineEndpointCells.roots F hcone height r) i) b → equation F height r t (curve j t))
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height r) (root (FlatAffineEndpointCells.roots F hcone height r) i))
    (s : ℝ) (hs : s ∈ gap (FlatAffineEndpointCells.roots F hcone height r) (rightGap _ i)) (hsb : s < b) :
    EndpointMidpoint.Matches {y | equation F height r (root (FlatAffineEndpointCells.roots F hcone height r) i) y} x.val (curve j s) ↔
      FiniteFiberSlab.Edge (equation F height r) curve (root (FlatAffineEndpointCells.roots F hcone height r) i) b
        (.inl j) (.inr (.inl x)) := by
  let R := FlatAffineEndpointCells.roots F hcone height r
  obtain ⟨c, hcgap, hsc, hcb⟩ := exists_rightGap_extension R i hs hsb
  have hac := root_lt_of_mem_rightGap R i hcgap
  have hsub : Icc (root R i) c ⊆ Icc (root R i) b := fun _ ht => ⟨ht.1, ht.2.trans hcb.le⟩
  have H := FlatAffineEndpointIncidence.left_iff F hcone height r hr hac ha curve
    (fun k => (hc k).mono hsub) (fun k t ht => hroot k t (hsub ht))
    (fun k t ht => FlatAffineEndpointCells.gap_avoids F hcone height r hr (root R i) ha
      (rightGap R i) t (right_interval_subset R i hcgap ht) k)
    j x ⟨s, root_lt_of_mem_rightGap R i hs, hsc⟩
  exact H

theorem right_iff {J : Type*} [Finite J] (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (i : Fin (FlatAffineEndpointCells.roots F hcone height r).card) {a : ℝ}
    (hb : SymbolicScaledSquarefree.scalarEvaluation (root (FlatAffineEndpointCells.roots F hcone height r) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (curve : J → ℝ → Fin (count F (pairFst r)) → ℝ)
    (hc : ∀ j, ContinuousOn (curve j) (Icc a (root (FlatAffineEndpointCells.roots F hcone height r) i)))
    (hroot : ∀ j t, t ∈ Icc a (root (FlatAffineEndpointCells.roots F hcone height r) i) → equation F height r t (curve j t))
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height r) (root (FlatAffineEndpointCells.roots F hcone height r) i))
    (s : ℝ) (hs : s ∈ gap (FlatAffineEndpointCells.roots F hcone height r) (leftGap _ i)) (has : a < s) :
    EndpointMidpoint.Matches {y | equation F height r (root (FlatAffineEndpointCells.roots F hcone height r) i) y} x.val (curve j s) ↔
      FiniteFiberSlab.Edge (equation F height r) curve a (root (FlatAffineEndpointCells.roots F hcone height r) i)
        (.inl j) (.inr (.inr x)) := by
  let R := FlatAffineEndpointCells.roots F hcone height r
  obtain ⟨c, hcgap, hac, hcs⟩ := exists_leftGap_extension R i hs has
  have hcb := lt_root_of_mem_leftGap R i hcgap
  have hsub : Icc c (root R i) ⊆ Icc a (root R i) := fun _ ht => ⟨hac.le.trans ht.1, ht.2⟩
  have H := FlatAffineEndpointIncidence.right_iff F hcone height r hr hcb hb curve
    (fun k => (hc k).mono hsub) (fun k t ht => hroot k t (hsub ht))
    (fun k t ht => FlatAffineEndpointCells.gap_avoids F hcone height r hr (root R i) hb
      (leftGap R i) t (left_interval_subset R i hcgap ht) k)
    j x ⟨s, hcs, lt_root_of_mem_leftGap R i hs⟩
  exact H

end LeanCanny.Connectivity.FlatAffineEndpointCellIncidence
