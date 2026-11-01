/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.SquaredDistanceFibers
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
/-! # Properness of polynomial squared distance in the old coordinate tuple -/
@[expose] public section
namespace LeanCanny.Geometry.SquaredDistanceFibers
open Set Metric
variable {n : ℕ}

theorem compact_sublevel (center : Fin n → ℝ) (r : ℝ) (hr : 0≤r) :
    IsCompact {x : Fin n → ℝ | value center x≤r} := by
  let E := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm
  have HE : {x : Fin n → ℝ | value center x≤r}=E ⁻¹' closedBall (E center) (Real.sqrt r) := by
    ext x
    change value center x≤r ↔ ‖E x-E center‖≤Real.sqrt r
    have HN : ‖E x-E center‖^2=value center x := norm_sq center x
    have HS := Real.sq_sqrt hr
    have H0 := norm_nonneg (E x-E center)
    have HR := Real.sqrt_nonneg r
    constructor <;> intro H <;> nlinarith
  rw [HE]
  exact E.isCompact_preimage.mpr (isCompact_closedBall _ _)

theorem proper_value (center : Fin n → ℝ) : IsProperMap (value center) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_value center,?_⟩
  intro K hK
  obtain ⟨r,hr⟩ := hK.bddAbove
  apply (compact_sublevel center (max r 0) (le_max_right _ _)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_value center))
  intro x hx
  exact (hr hx).trans (le_max_left _ _)

end LeanCanny.Geometry.SquaredDistanceFibers
