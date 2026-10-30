/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabBranchParents
public import LeanCanny.Connectivity.FlatAffineSlabCoordinateTests
public import LeanCanny.Encoding.FlatAffineBranchCoordinateSign

/-! # A native sample sign decides a coordinate sign on the entire branch -/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchChoice.value FlatAffineEndpointRankWord.anchorPoint
  Family.descriptor

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

omit [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)] in
theorem Family.sign_prepare_packet (B : Family F cone height c)
    (side : Bool) (j : Index F cone height c) (i : Fin (count F (original c))) :
    FlatAffineBranchCoordinateSign.prepare F cone height (pair (B.sampleQuery side j) (BinaryNatCode.encode i.val)) =
      pair (pair (source c) (B.selectedWord side j))
        (BinaryNatCode.encode (FlatAffineEndpointFiniteProjection.slot F (source c) 0 i).val) := by
  rw [FlatAffineBranchCoordinateSign.prepare_packet]
  have HS : FlatAffineEndpointBranchLabels.source (B.sampleQuery side j) = source c := by
    simp only [Family.sampleQuery, FlatAffineEndpointBranchLabels.source, pairFst_pair]
  rw [HS, FlatAffineEndpointCopyEquality.slotWord, FlatAffineEndpointFiniteSide.coordinate_encode]
  rfl

theorem Family.sample_sign_packet (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) (i : Fin (count F (original c))) :
    FlatAffineBranchCoordinateSign.value F cone height (pair (B.sampleQuery side j) (BinaryNatCode.encode i.val)) =
      InfinitesimalSign.encode (SignType.sign (B.curve j (sampleValue F cone height side c) i)) := by
  rw [FlatAffineBranchCoordinateSign.value, Function.comp_apply, B.sign_prepare_packet]
  rw [SquareSampleCompleteCoordinateSign.packet _ _ _ (B.selected_valid hc side j)]
  apply congrArg (fun x : ℝ => InfinitesimalSign.encode (SignType.sign x))
  exact ((congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (source c) z 0 i)
    (FlatAffineEndpointRankWord.anchorPoint_packet F cone height (source c) (B.selectedWord side j) (B.selected_valid hc side j))).symm).trans
      (congrFun (B.selected_current hc side j) i)

theorem Family.sign_reader_packet (B : Family F cone height c) (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (side : Bool) (j : Index F cone height c) (i : Fin (count F (original c)))
    (t : Ioo (endpointValue F cone height false c) (endpointValue F cone height true c)) :
    FlatAffineBranchCoordinateSign.value F cone height (pair (B.sampleQuery side j) (BinaryNatCode.encode i.val)) =
      InfinitesimalSign.encode (SignType.sign (B.curve j t.val i)) := by
  rw [B.sample_sign_packet hc side j i]
  apply congrArg InfinitesimalSign.encode
  have H := B.coordinate_tests_iff hc j i ⟨_, FlatAffineSlabGraphContext.samples_between F cone height side c hc⟩ t
  rcases lt_trichotomy (B.curve j (sampleValue F cone height side c) i) 0 with hn | hz | hp
  · rw [sign_neg hn, sign_neg (H.2.1.mp hn)]
  · rw [sign_eq_zero_iff.mpr hz, sign_eq_zero_iff.mpr (H.1.mp hz)]
  · rw [sign_pos hp, sign_pos (H.2.2.mp hp)]

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
