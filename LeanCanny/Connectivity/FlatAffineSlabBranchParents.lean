/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphBranchLabels
public import LeanCanny.Encoding.FlatAffineBranchChildSamples

/-! # Computed recursive parents denote the requested geometric branch point

Descriptor search may choose any auxiliary joint tuple. Native height binding
and coordinate-rank injectivity force its current point to be precisely the
constructed curve at the requested retained sample.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord sampleWord)
open FlatAffineSlabGraphArcs (Index)
open FlatAffineSlabGraphContext (sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchChoice.value FlatAffineEndpointRankWord.word

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

noncomputable def Family.sampleQuery (B : Family F cone height c) (side : Bool) (j : Index F cone height c) : List Bool :=
  pair (pair (source c) (pair (sampleWord side c) (gapWord c))) (B.descriptor side j)
noncomputable def Family.selectedWord (B : Family F cone height c) (side : Bool) (j : Index F cone height c) : List Bool :=
  FlatAffineBranchChoice.value F cone height (B.sampleQuery side j)

theorem Family.selected_spec (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) :
    pair (pair (source c) (B.selectedWord side j)) (pair (sampleWord side c) (gapWord c)) ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
      FlatAffineEndpointRankWord.word F cone height (pair (source c) (B.selectedWord side j)) = B.descriptor side j := by
  have H := FlatAffineBranchChoice.value_spec F cone height (B.sampleQuery side j)
    ((B.labels_iff hc side _).mpr ⟨j, rfl⟩)
  simpa only [Family.sampleQuery, Family.selectedWord, FlatAffineEndpointBranchLabels.slabQuery,
    FlatAffineEndpointBranchLabels.candidateQuery, FlatAffineEndpointBranchLabels.source,
    FlatAffineEndpointBranchLabels.samplePacket, FlatAffineEndpointBranchLabels.descriptor,
    pairFst_pair, pairSnd_pair] using H

theorem Family.selected_valid (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) (B.selectedWord side j) := by
  simpa only [pairFst_pair, pairSnd_pair] using FlatAffineEndpointSampleSlab.joint_valid F cone height _ (B.selected_spec hc side j).1

theorem Family.selected_current (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) :
    FlatAffineEndpointRankWord.currentValue F cone height (source c) (B.selectedWord side j) = B.curve j (sampleValue F cone height side c) := by
  have hw := B.selected_valid hc side j
  have SW := (B.selected_spec hc side j).1
  unfold FlatAffineEndpointSampleSlab.language at SW
  have HE := (FlatAffineEndpointFiniteHeights.sample_packet F cone height (source c) (B.selectedWord side j) (sampleWord side c)
    hc.1 hw (FlatAffineSlabGraphContext.sample_label_valid F cone height side c hc)).mp (by
      simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
        pairFst_pair, pairSnd_pair] using SW.2.1)
  have HT : FlatAffineEndpointRankWord.sampleValue F cone height (source c) (B.selectedWord side j) = sampleValue F cone height side c :=
    (congrArg (FlatAffineEndpointFiniteProjection.sample F (source c))
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height (source c) (B.selectedWord side j) hw)).trans
        (HE.trans (FlatAffineSlabGraphContext.sampleValue_packet F cone height side c hc).symm)
  have HR := FlatAffineEndpointRankWord.current_in_fiber F cone height (source c) (B.selectedWord side j) hc.1 hw
  rw [HT] at HR
  obtain ⟨k, hk⟩ := B.sample_cover hc side _ HR
  have VW := FlatAffineEndpointRankWord.view_at_sample F cone height B.points k (source c) (B.selectedWord side j)
    (sampleValue F cone height side c) (B.sample_roots hc side) (B.sample_cover hc side) HT hk.symm
  have HC := FlatAffineEndpointRankWord.word_eq_implies_current_eq F cone height B.points k j (source c)
    (B.selectedWord side j) (B.reference side j) hc.1 hw (B.valid side j) VW (B.view hc side j)
    (HT.trans (B.sample side j).symm) (B.selected_spec hc side j).2
  exact HC.trans (B.current side j)

noncomputable def Family.sampleParent (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) : NamedRationalParents.Root (FlatAffineCurrentNamedParents.source F cone height) (source c) :=
  FlatAffineCurrentNamedParents.root F cone height (source c) (B.selectedWord side j) hc.1 (B.selected_valid hc side j)

theorem Family.sampleParent_name (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) :
    (FlatAffineCurrentNamedParents.source F cone height).descriptor (source c) (B.sampleParent hc side j) = B.selectedWord side j :=
  FlatAffineCurrentNamedParents.root_name F cone height (source c) (B.selectedWord side j) hc.1 (B.selected_valid hc side j)

theorem Family.sampleParent_point (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) (i : Fin (count F (FlatAffineSlabGraphArcs.original c))) :
    RationalCoordinateFamily.point (FlatAffineCurrentNamedParents.source F cone height).coordinates (source c)
      (B.sampleParent hc side j).val i.val = B.curve j (sampleValue F cone height side c) i :=
  (FlatAffineCurrentNamedParents.root_point F cone height (source c) (B.selectedWord side j) hc.1 (B.selected_valid hc side j) i).trans
    (congrFun (B.selected_current hc side j) i)

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
