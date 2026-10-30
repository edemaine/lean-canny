/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftPrefixInput
public import LeanCanny.Connectivity.FlatAffineSlabGraphBranches

/-! # Actual slab branches retain their frozen ancestry through both endpoints

The stage of the varied row determines the unchanged prefix. Every constructed
critical branch has that same prefix at every closed-slab parameter, including
singular endpoint limits. Its two native joint sample labels consequently
project to the same frozen ancestor point.
-/

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
set_option maxHeartbeats 400000

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}

theorem Family.frozen_prefix (B : Family F cone height c)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (j : Index F cone height c)
    (s t : Icc (endpointValue F cone height false c) (endpointValue F cone height true c)) :
    B.curve j s.val ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
      (FlatAffineShiftPrefixInput.depth_le F height) (original c) =
    B.curve j t.val ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
      (FlatAffineShiftPrefixInput.depth_le F height) (original c) := by
  let : PreconnectedSpace (Icc (endpointValue F cone height false c) (endpointValue F cone height true c)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact FlatAffineShiftPrefixInput.constant F cone height (original c) hold
    (fun r : Icc (endpointValue F cone height false c) (endpointValue F cone height true c) => r.val)
    (fun r => B.curve j r.val) (continuousOn_iff_continuous_domRestrict.mp (B.continuous j))
    (fun r => B.roots j r.val r.property) s t

theorem Family.frozen_prefix_anchor (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (j : Index F cone height c)
    (s : Icc (endpointValue F cone height false c) (endpointValue F cone height true c)) :
    B.curve j s.val ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
      (FlatAffineShiftPrefixInput.depth_le F height) (original c) =
    j.val ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
      (FlatAffineShiftPrefixInput.depth_le F height) (original c) := by
  have HT := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height false c hc)
  have H := B.frozen_prefix hold j s ⟨sampleValue F cone height false c, HT⟩
  rw [B.anchor] at H
  exact H

theorem Family.reference_prefixes (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (j : Index F cone height c) :
    FlatAffineEndpointRankWord.currentValue F cone height (source c) (B.reference false j) ∘
      FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
        (FlatAffineShiftPrefixInput.depth_le F height) (original c) =
    FlatAffineEndpointRankWord.currentValue F cone height (source c) (B.reference true j) ∘
      FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
        (FlatAffineShiftPrefixInput.depth_le F height) (original c) := by
  rw [B.current, B.current]
  exact B.frozen_prefix hold j
    ⟨sampleValue F cone height false c, Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height false c hc)⟩
    ⟨sampleValue F cone height true c, Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height true c hc)⟩

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
