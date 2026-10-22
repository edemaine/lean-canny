/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UniformExtendedProjectionDirections
public import LeanCanny.Geometry.TubeUniformRationalDirections

/-! # Uniform rational tube directions over extension fields

A single nearby rational direction gives finite extended critical fibers for
all active tubes throughout a common positive level interval, in every
extension field of the reals. The reciprocal equation already excludes
nonregular points, so no regular-level hypothesis is needed here.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set MvPolynomial
open scoped Topology
universe uL
variable {ι : Type*} [Fintype ι]

theorem exists_uniform_rational_finite_extended_direction_near (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (hv : v (base ι) = 1)
    (U : Set (Coordinate ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex (base ι) → ℚ,
      ProjectionCritical.rationalDirection (base ι) u ∈ U ∧ ∃ a : ℝ, 0 < a ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < a →
          ∀ (L : Type uL) [Field L] [Algebra ℝ L], ∀ s : Finset (PolynomialPerturbation.Constraint ι),
            {z : Option (Coordinate ι) → L | ∀ j, aeval z
              (Algebra.GenericProjectionFinite.equation
                ((polynomial p s).map ((algebraMap ℝ L).comp (coefficientMap epsilon delta alpha)))
                (base ι) (Algebra.ProjectionFiniteSpecialization.normalizedDirection (base ι)
                  (fun i => algebraMap ℝ L (u i : ℝ))) j) = 0}.Finite := by
  classical
  obtain ⟨u, hu, a, ha, hf⟩ := ProjectionCritical.exists_common_rational_extended_direction_in_extensions
    (fun s => realEnergy p s epsilon delta) (base ι) v hv U hU
  refine ⟨u, hu, a, ha, ?_⟩
  intro alpha hp hl L _ _ s
  have hlevel : Algebra.LevelProjectionSpecialization.levelPolynomial (realEnergy p s epsilon delta)
      (algebraMap ℝ L alpha) =
      (polynomial p s).map ((algebraMap ℝ L).comp (coefficientMap epsilon delta alpha)) := by
    calc
      _ = (Algebra.LevelProjectionSpecialization.levelPolynomial (realEnergy p s epsilon delta) alpha).map
          (algebraMap ℝ L) := by
        simp only [Algebra.LevelProjectionSpecialization.levelPolynomial, Algebra.algebraMap_self,
          MvPolynomial.map_id, map_sub, MvPolynomial.map_C]
      _ = _ := by rw [level_realEnergy, MvPolynomial.map_map]
  have h := hf alpha hp hl L s
  rw [hlevel] at h
  exact h
end LeanCanny.Geometry.TubePolynomial
