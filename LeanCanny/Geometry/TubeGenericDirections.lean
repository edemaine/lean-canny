/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeParameterField
public import LeanCanny.Geometry.GenericDirectionNeighborhood

/-! # Dense directions giving finite root sets for every active tube

For each sufficiently small positive tube level, normalized real directions
with finite projection root sets for all active sets occur in every
neighborhood of every normalized direction. The field and direction may
depend on the level; effective selection is not supplied.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set
open scoped Topology

variable {ι : Type*} [Fintype ι]

theorem exists_finite_projection_directions_near (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ v : Coordinate ι → ℝ, v (base ι) = 1 →
        ∀ U : Set (Coordinate ι → ℝ), U ∈ nhds v →
          ∃ w ∈ U, w (base ι) = 1 ∧
            ∀ s : Finset (PolynomialPerturbation.Constraint ι), (projectionRootSet p s epsilon delta alpha w).Finite := by
  obtain ⟨a, ha, hr⟩ := exists_common_regular_interval p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs v hv U hU
  obtain ⟨w, hwU, hw, hind⟩ := IndependentRealDirections.exists_normalized_near
    (K := parameterField epsilon delta alpha) (base ι) v hv U hU
  exact ⟨w, hwU, hw, fun s => finite_projectionRootSet_over_parameterField p s epsilon delta alpha w hw hind
    (fun x hx => hr alpha hp hs s x hx)⟩

theorem exists_finite_projection_directions (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧
        ∀ s : Finset (PolynomialPerturbation.Constraint ι), (projectionRootSet p s epsilon delta alpha v).Finite := by
  obtain ⟨a, ha, hr⟩ := exists_finite_projection_directions_near p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs
  obtain ⟨v, _, hv⟩ := hr alpha hp hs (fun _ => 1) rfl univ Filter.univ_mem
  exact ⟨v, hv⟩

end LeanCanny.Geometry.TubePolynomial
