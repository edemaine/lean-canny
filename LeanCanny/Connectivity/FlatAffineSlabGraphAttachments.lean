/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphBranchLabels
public import LeanCanny.Connectivity.FlatAffineEndpointDescriptorIncidence
public import LeanCanny.Encoding.FlatAffineSlabGraphEdges
public import LeanCanny.Encoding.FlatAffineEndpointMarkerComplete

/-! # Native slab edges identify the constructed curves' actual endpoints

Only the accepted context and an accepted endpoint marker are supplied. The
curve family, its sample references, adjacency, and exceptional-set avoidance
have already been constructed from the original source.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord endpointWord sampleWord)
open FlatAffineSlabGraphArcs (original equation Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

noncomputable def markerPoint (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w : List Bool) : Fin (count F (original c)) → ℝ :=
  FlatAffineEndpointFiniteProjection.copy F (source c) (FlatAffineEndpointRankWord.anchorPoint F cone height (source c) w) 1

theorem markerPoint_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) w) :
    markerPoint F cone height c w = FlatAffineEndpointFiniteProjection.copy F (source c)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).val 1 :=
  congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (source c) z 1)
    (FlatAffineEndpointRankWord.anchorPoint_packet F cone height (source c) w hw)

omit [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)] in
theorem markerPoint_in_fiber (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (w : List Bool)
    (hm : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    equation F height c (endpointValue F cone height side c) (markerPoint F cone height c w) := by
  have hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) w := by
    simpa only [FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointMarkers.joint_valid F cone height _ hm
  rw [markerPoint_packet F cone height c w hw]
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F (source c)) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).val
  have HZ := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) (source c) hc.1 z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).property
  have HE := (FlatAffineEndpointMarkers.packet F cone height (source c) (endpointWord side c) w hc.1 hw
    (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc)).mp hm
  intro i
  have H := (FlatAffineEndpointFiniteProjection.equations F height (source c) z HZ).2.2 (1 : Fin 3) i
  rw [HE, ← FlatAffineSlabGraphContext.endpointValue_packet F cone height side c hc] at H
  simpa using H

omit [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)] in
theorem markerPoint_complete (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool)
    (x : Fin (count F (original c)) → ℝ) (hx : equation F height c (endpointValue F cone height side c) x) :
    ∃ w, pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height ∧
      markerPoint F cone height c w = x := by
  have HX : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (source c)
      ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst (source c)) (endpointWord side c)
        (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc)).val (0 : Fin 1)) := by
    rw [← FlatAffineSlabGraphContext.endpointValue_packet F cone height side c hc]
    exact hx
  obtain ⟨w, hw, hm, he⟩ := FlatAffineEndpointMarkers.complete F cone height (source c) (endpointWord side c) hc.1
    (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc) x HX
  exact ⟨w, hm, (markerPoint_packet F cone height c w hw).trans he⟩

omit [LinearOrder (Index F cone height c)] in
theorem Family.matches_endpoint_iff (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (j : Index F cone height c)
    (x : Fin (count F (original c)) → ℝ) (hx : equation F height c (endpointValue F cone height side c) x) :
    EndpointMidpoint.Matches {y | equation F height c (endpointValue F cone height side c) y}
      x (B.curve j (sampleValue F cone height side c)) ↔ B.curve j (endpointValue F cone height side c) = x := by
  obtain ⟨i, hi⟩ := OrderedRealCells.exists_root (FlatAffineSlabGraphContext.refinedRoots F cone height c) _
    (FlatAffineSlabGraphContext.adjacent_ranks F cone height side c hc).1
  dsimp only [FlatAffineSlabGraphContext.refinedRoots] at i hi
  have HROOT : SymbolicScaledSquarefree.scalarEvaluation
      (OrderedRealCells.root (FlatAffineEndpointCells.roots F cone height (pairFst (source c))) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (original c)) = 0 := by
    rw [hi]
    exact FlatAffineSlabGraphContext.endpoint_root F cone height side c hc
  let x' : FiniteFiberSlab.Fiber (FlatAffineEndpointMidpoint.equation F height (pairFst (source c)))
      (OrderedRealCells.root (FlatAffineEndpointCells.roots F cone height (pairFst (source c))) i) :=
    ⟨x, by rw [hi]; exact hx⟩
  have HG := FlatAffineSlabGraphContext.refined_gap F cone height side c hc i hi
  have HB := FlatAffineSlabGraphContext.samples_between F cone height side c hc
  cases side
  · have H := FlatAffineEndpointCellIncidence.left_iff F cone height (pairFst (source c)) hc.1.1 i HROOT B.curve
      (fun k => by simpa only [hi] using B.continuous k)
      (fun k t ht => B.roots k t (by simpa only [hi] using ht)) j x' (sampleValue F cone height false c) HG HB.2
    simp only [hi, FiniteFiberSlab.Edge] at H
    exact H
  · have H := FlatAffineEndpointCellIncidence.right_iff F cone height (pairFst (source c)) hc.1.1 i HROOT B.curve
      (fun k => by simpa only [hi] using B.continuous k)
      (fun k t ht => B.roots k t (by simpa only [hi] using ht)) j x' (sampleValue F cone height true c) HG HB.1
    simp only [hi, FiniteFiberSlab.Edge] at H
    exact H

theorem Family.attachment_iff (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (j : Index F cone height c)
    (w : List Bool)
    (hm : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    FlatAffineEndpointIncidenceQuery.record (source c) (endpointWord side c) (sampleWord side c) (gapWord c)
      (B.descriptor false j) w ∈ FlatAffineEndpointIncidenceQuery.language F cone height (!side) ↔
      B.curve j (endpointValue F cone height side c) = markerPoint F cone height c w := by
  have hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) w := by
    simpa only [FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointMarkers.joint_valid F cone height _ hm
  rw [markerPoint_packet F cone height c w hw]
  let x := FlatAffineEndpointFiniteProjection.copy F (source c)
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).val 1
  have HM : FlatAffineEndpointIncidenceQuery.record (source c) (endpointWord side c) (sampleWord side c) (gapWord c)
      (B.descriptor side j) w ∈ FlatAffineEndpointIncidenceQuery.language F cone height (!side) ↔
      EndpointMidpoint.Matches
        (FlatAffineEndpointFiniteMatching.endpointFiber F height (source c)
          ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
            (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst (source c)) (endpointWord side c)
            (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc)).val (0 : Fin 1))) x
        (FlatAffineEndpointFiniteProjection.copy F (source c)
          (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c)
            (B.reference side j) (B.valid side j)).val 0) :=
    ⟨FlatAffineEndpointDescriptorMatching.sound F cone height B.points j (source c) (B.reference side j) w
      (endpointWord side c) (sampleWord side c) (gapWord c) hc.1 (B.valid side j) hw
      (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc) (B.view hc side j) (B.slab side j) hm (!side),
      FlatAffineEndpointDescriptorMatching.complete F cone height B.points j (source c) (B.reference side j) w
      (endpointWord side c) (sampleWord side c) (gapWord c) hc.1 (B.valid side j) hw
      (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc) (B.view hc side j) (B.slab side j) hm (!side)
      (B.adjacent side j)⟩
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F (source c)) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).val
  have HZ := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) (source c) hc.1 z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).property
  have HE := (FlatAffineEndpointMarkers.packet F cone height (source c) (endpointWord side c) w hc.1 hw
    (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc)).mp hm
  have HR : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (source c) (endpointValue F cone height side c) := by
    intro i
    have H := (FlatAffineEndpointFiniteProjection.equations F height (source c) z HZ).2.2 (1 : Fin 3) i
    rw [HE, ← FlatAffineSlabGraphContext.endpointValue_packet F cone height side c hc] at H
    simpa using H
  rw [← FlatAffineSlabGraphContext.endpointValue_packet F cone height side c hc] at HM
  have HC : FlatAffineEndpointFiniteProjection.copy F (source c)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c)
        (B.reference side j) (B.valid side j)).val 0 = B.curve j (sampleValue F cone height side c) :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (source c) z 0)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height (source c) (B.reference side j) (B.valid side j))).symm.trans (B.current side j)
  rw [HC, B.descriptor_same hc side j] at HM
  exact HM.trans (B.matches_endpoint_iff hc side j x HR)

theorem Family.branch_marker_iff (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (j : Index F cone height c)
    (w : List Bool)
    (hm : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    pair c (pair (FlatAffineSlabGraphCodes.branchNode F cone height c (B.descriptor false j))
      (FlatAffineSlabGraphCodes.markerNode F cone height side c w)) ∈ FlatAffineSlabGraph.edgeLanguage F cone height ↔
      B.curve j (endpointValue F cone height side c) = markerPoint F cone height c w := by
  have HB := (B.labels_iff hc false (B.descriptor false j)).mpr ⟨j, rfl⟩
  exact (FlatAffineSlabGraph.branch_marker_iff F cone height side c (B.descriptor false j) w HB hm).trans
    (B.attachment_iff hc side j w hm)

theorem Family.marker_branch_iff (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (j : Index F cone height c)
    (w : List Bool)
    (hm : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    pair c (pair (FlatAffineSlabGraphCodes.markerNode F cone height side c w)
      (FlatAffineSlabGraphCodes.branchNode F cone height c (B.descriptor false j))) ∈ FlatAffineSlabGraph.edgeLanguage F cone height ↔
      B.curve j (endpointValue F cone height side c) = markerPoint F cone height c w := by
  have HB := (B.labels_iff hc false (B.descriptor false j)).mpr ⟨j, rfl⟩
  exact (FlatAffineSlabGraph.marker_branch_iff F cone height side c (B.descriptor false j) w HB hm).trans
    (B.attachment_iff hc side j w hm)

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
