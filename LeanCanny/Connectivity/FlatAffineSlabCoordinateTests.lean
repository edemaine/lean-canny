/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphBranches
public import LeanCanny.Geometry.FlatAffineHeightCoordinateSigns

/-! # Accepted native contexts make all coordinate zero tests persistent

The computed slab polynomial now contains coordinate trailing factors. A
single interior sample therefore decides every coordinate zero and strict
sign along a constructed branch, including its critical multipliers.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}

theorem Family.coordinate_tests_iff (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (j : Index F cone height c)
    (i : Fin (count F (original c)))
    (s t : Ioo (endpointValue F cone height false c) (endpointValue F cone height true c)) :
    (B.curve j s.val i = 0 ↔ B.curve j t.val i = 0) ∧
      (B.curve j s.val i < 0 ↔ B.curve j t.val i < 0) ∧ (0 < B.curve j s.val i ↔ 0 < B.curve j t.val i) := by
  apply FlatAffineHeightCoordinateSigns.tests_iff F height (original c) (B.curve j)
    ((B.continuous j).mono Ioo_subset_Icc_self) ?_ (FlatAffineSlabGraphArcs.coordinate_trailing_avoids F cone height c hc) i s t
  intro v hv
  exact (FlatAffineSlabGraphArcs.value_iff_equation F height c v (B.curve j v)).mpr (B.roots j v (Ioo_subset_Icc_self hv))

theorem Family.coordinate_ne_zero (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (j : Index F cone height c)
    (i : Fin (count F (original c))) (h0 : B.curve j (sampleValue F cone height side c) i ≠ 0)
    (t : Ioo (endpointValue F cone height false c) (endpointValue F cone height true c)) : B.curve j t.val i ≠ 0 := by
  intro ht
  exact h0 ((B.coordinate_tests_iff hc j i ⟨_, FlatAffineSlabGraphContext.samples_between F cone height side c hc⟩ t).1.mpr ht)

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
