/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphContextGeometry

/-! # Accepted native contexts describe one actual bounded original slab

Both refined adjacent samples lie in the checked original gap. Refinement
then identifies their retained endpoints with that gap's two boundary roots.
Thus endpoint order and open-interval membership follow from native checks.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphContext
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem endpoint_indices (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) (hc : c ∈ language F cone height) :
    ∃ i j : Fin (roots F cone height c).card,
      root (roots F cone height c) i = endpointValue F cone height false c ∧
      root (roots F cone height c) j = endpointValue F cone height true c ∧
      gapIndex F cone height c hc = rightGap (roots F cone height c) i ∧
      gapIndex F cone height c hc = leftGap (roots F cone height c) j := by
  have hs := original_subset_refined F cone height c hc
  obtain ⟨i, hi⟩ := exists_root (roots F cone height c) _ (endpoint_mem F cone height false c hc)
  obtain ⟨j, hj⟩ := exists_root (roots F cone height c) _ (endpoint_mem F cone height true c hc)
  obtain ⟨u, hu⟩ := exists_root (refinedRoots F cone height c) _ (hs (endpoint_mem F cone height false c hc))
  obtain ⟨v, hv⟩ := exists_root (refinedRoots F cone height c) _ (hs (endpoint_mem F cone height true c hc))
  have hL : sampleValue F cone height false c ∈ gap (refinedRoots F cone height c) (rightGap _ u) :=
    refined_gap F cone height false c hc u hu
  have hR : sampleValue F cone height true c ∈ gap (refinedRoots F cone height c) (leftGap _ v) :=
    refined_gap F cone height true c hc v hv
  have L := rightGap_refines (roots F cone height c) (refinedRoots F cone height c) hs i u (hi.trans hu.symm) hL
  have R := leftGap_refines (roots F cone height c) (refinedRoots F cone height c) hs j v (hj.trans hv.symm) hR
  exact ⟨i, j, hi, hj,
    same_gap_eq _ _ _ (sample_in_gap F cone height false c hc) L,
    same_gap_eq _ _ _ (sample_in_gap F cone height true c hc) R⟩

theorem endpoints_lt (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) (hc : c ∈ language F cone height) :
    endpointValue F cone height false c < endpointValue F cone height true c := by
  obtain ⟨i, j, hi, hj, hL, hR⟩ := endpoint_indices F cone height c hc
  have H : i.val + 1 = j.val := congrArg Fin.val (hL.symm.trans hR)
  have hij : i < j := by change i.val < j.val; omega
  simpa only [hi, hj] using root_strictMono (roots F cone height c) hij

theorem gap_eq_interval (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) (hc : c ∈ language F cone height) :
    gap (roots F cone height c) (gapIndex F cone height c hc) =
      Set.Ioo (endpointValue F cone height false c) (endpointValue F cone height true c) := by
  obtain ⟨i, j, hi, hj, hL, hR⟩ := endpoint_indices F cone height c hc
  have HL : (gapIndex F cone height c hc).val = i.val + 1 := congrArg Fin.val hL
  have HR : (gapIndex F cone height c hc).val = j.val := congrArg Fin.val hR
  have h0 : 0 < (gapIndex F cone height c hc).val := by omega
  have hk : (gapIndex F cone height c hc).val < (roots F cone height c).card := HR ▸ j.isLt
  have I : (⟨(gapIndex F cone height c hc).val - 1, by omega⟩ : Fin (roots F cone height c).card) = i := by
    apply Fin.ext
    change (gapIndex F cone height c hc).val - 1 = i.val
    omega
  have J : (⟨(gapIndex F cone height c hc).val, hk⟩ : Fin (roots F cone height c).card) = j := Fin.ext HR
  simpa only [I, J, hi, hj] using gap_interior (gapIndex F cone height c hc) h0 hk

theorem samples_between (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    sampleValue F cone height side c ∈ Set.Ioo (endpointValue F cone height false c) (endpointValue F cone height true c) := by
  rw [← gap_eq_interval F cone height c hc]
  exact sample_in_gap F cone height side c hc

end LeanCanny.Encoding.FlatAffineSlabGraphContext
