/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphBranches
public import LeanCanny.Connectivity.FlatAffineEndpointBranchRelation

/-! # Native descriptors enumerate the constructed slab branches

The two checked samples give exactly the same injective set of descriptors.
The family and its reference labels come from the original source equations.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord sampleWord)
open FlatAffineSlabGraphArcs (original equation Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}

noncomputable def Family.points (B : Family F cone height c) (s : List Bool)
    (t : ℝ) (j : Index F cone height c) : Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ :=
  if h : s = source c then fun i => B.curve j t (Fin.cast (by subst s; rfl) i) else 0

theorem Family.points_packet (B : Family F cone height c) (t : ℝ) (j : Index F cone height c) :
    B.points (source c) t j = B.curve j t := by
  simp [Family.points]

noncomputable def Family.descriptor (B : Family F cone height c) (side : Bool) (j : Index F cone height c) : List Bool :=
  FlatAffineEndpointRankWord.word F cone height (pair (source c) (B.reference side j))

theorem Family.sample_roots (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) :
    B.points (source c) (sampleValue F cone height side c) j ∈
      FlatAffineEndpointFiniteMatching.endpointFiber F height (source c) (sampleValue F cone height side c) := by
  rw [B.points_packet]
  exact B.roots j _ (Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height side c hc))

theorem Family.sample_cover (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (x : Fin (count F (original c)) → ℝ)
    (hx : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (source c) (sampleValue F cone height side c)) :
    ∃ j, B.points (source c) (sampleValue F cone height side c) j = x := by
  obtain ⟨j, hj, _⟩ := (B.complete ⟨_, FlatAffineSlabGraphContext.samples_between F cone height side c hc⟩ x).mp hx
  exact ⟨j, (B.points_packet _ _).trans hj⟩

theorem Family.view (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) :
    FlatAffineEndpointRankWord.BranchView F cone height B.points j (source c) (B.reference side j) := by
  apply FlatAffineEndpointRankWord.view_at_sample F cone height B.points j (source c) (B.reference side j)
    (sampleValue F cone height side c) (B.sample_roots hc side) (B.sample_cover hc side) (B.sample side j)
  exact (B.current side j).trans (B.points_packet _ _).symm

variable [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

theorem Family.labels_iff (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (d : List Bool) :
    pair (pair (source c) (pair (sampleWord side c) (gapWord c))) d ∈ FlatAffineEndpointBranchLabels.language F cone height ↔
      ∃ j, B.descriptor side j = d := by
  exact FlatAffineEndpointBranchLabels.language_iff_fiber F cone height B.points (source c) (sampleWord side c) (gapWord c) hc.1
    (FlatAffineSlabGraphContext.sample_label_valid F cone height side c hc) (sampleValue F cone height side c)
    (FlatAffineSlabGraphContext.sampleValue_packet F cone height side c hc).symm
    (B.sample_roots hc side) (B.sample_cover hc side) (B.reference side) (B.valid side) (B.sample side)
    (fun j => (B.current side j).trans (B.points_packet _ _).symm) (B.slab side) d

theorem Family.descriptors_injective (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) :
    Function.Injective (B.descriptor side) := by
  apply FlatAffineEndpointBranchLabels.words_injective F cone height B.points (source c) hc.1 (sampleValue F cone height side c)
    (B.sample_roots hc side) (B.sample_cover hc side) (B.reference side) (B.valid side) (B.sample side)
    (fun j => (B.current side j).trans (B.points_packet _ _).symm)
  have H := B.injective ⟨_, FlatAffineSlabGraphContext.samples_between F cone height side c hc⟩
  intro j k he
  exact H ((B.points_packet _ j).symm.trans (he.trans (B.points_packet _ k)))

theorem Family.descriptor_same (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (j : Index F cone height c) :
    B.descriptor side j = B.descriptor false j := by
  apply FlatAffineEndpointRankWord.word_eq_of_same_branch F cone height B.points j (source c)
    (B.reference side j) (B.reference false j) hc.1 (B.valid side j) (B.valid false j) (B.view hc side j) (B.view hc false j)
    (FlatAffineHeightGrid.coordinate F height (original c))
  · intro t ht i
    apply FlatAffineEndpointBranchRelation.coordinate_avoid F cone height (source c) t _ i
    apply OrderedRealCells.gap_no_root _ (FlatAffineSlabGraphContext.gapIndex F cone height c hc)
    rw [FlatAffineSlabGraphContext.gap_eq_interval F cone height c hc]
    exact ht
  · intro k
    simpa only [B.points_packet] using (B.continuous k).mono Ioo_subset_Icc_self
  · intro k t ht i
    rw [B.points_packet]
    exact FlatAffineEndpointBranchRelation.coordinate_root F height (pairFst (source c)) t _
      (B.roots k t (Ioo_subset_Icc_self ht)) i
  · rw [B.sample]
    exact FlatAffineSlabGraphContext.samples_between F cone height side c hc
  · rw [B.sample]
    exact FlatAffineSlabGraphContext.samples_between F cone height false c hc

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
