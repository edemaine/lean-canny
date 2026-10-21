/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCompiledAffineRoots
public import LeanCanny.Geometry.TubeUniformExtendedDirections
public import LeanCanny.ETR.TubeCharacteristicFiniteBounds

/-! # Geometric finiteness for the compiled characteristic polynomial

A nearby rational direction works over every extension field throughout a
common small positive tube-level interval. Any rational substitution with
nonzero denominators that realizes those perturbation parameters and that
direction has a finite compiled affine fiber. Over an algebraically closed
field, the lowest quotient coefficient consequently vanishes at every root.
The parameter identities are explicit; constructing bounded encoded readers
that satisfy them remains an algorithmic obligation.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCompiledAffineRoots
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open Set MvPolynomial
open scoped Topology Classical
universe uL

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

theorem exists_uniform_rational_direction_finite_compiled_fibers
    (source active : List Bool → List Bool) (ell : List Bool → ℕ → ℤ) (c : List Bool)
    (epsilon delta : ℝ) (v : TubeSource.Coordinate (source c) → ℝ)
    (hv : v (TubePolynomial.base _) = 1)
    (U : Set (TubeSource.Coordinate (source c) → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : ProjectionFiniteSpecialization.DirectionIndex (TubePolynomial.base (Fin (TubeIndexed.arity (source c)))) → ℚ,
      ProjectionCritical.rationalDirection (TubePolynomial.base _) u ∈ U ∧ ∃ a : ℝ, 0 < a ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < a → ∀ (L : Type uL) [Field L] [Algebra ℝ L],
          ∀ (n d : List Bool → ℕ → Polynomial ℤ) (t : L),
            (∀ i, i < TubeParameter.parameterCount (source c) →
              (d c i).eval₂ (Int.castRingHom L) t ≠ 0) →
            TubeRegularFiber.coefficientMap (source c)
                (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom L) t) =
              (algebraMap ℝ L).comp (TubePolynomial.coefficientMap epsilon delta alpha) →
            TubeRegularFiber.direction (source c)
                (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom L) t) =
              ProjectionFiniteSpecialization.normalizedDirection (TubePolynomial.base _)
                (fun i => algebraMap ℝ L (u i : ℝ)) →
            (zeroLocus L (ProjectiveNullstellensatz.generated
              (TubeCharacteristicQuotient.finiteSystem source active n d ell c t))).Finite := by
  obtain ⟨u, hu, a, ha, hf⟩ := TubePolynomial.exists_uniform_rational_finite_extended_direction_near
    (CompactSource.polynomial (source c)) epsilon delta v hv U hU
  refine ⟨u, hu, a, ha, ?_⟩
  intro alpha hp hl L _ _ n d t hd hc hv
  apply finite_fiber_of_finite_extended_critical source active n d ell c t hd
  · rw [hv]
    exact dite_eq_left rfl
  · have h := hf alpha hp hl L (activeSet (TubeIndexed.arity (source c)) (active c))
    have he : TubeRegularFiber.specializedPolynomial (source c)
        (activeSet (TubeIndexed.arity (source c)) (active c))
        (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom L) t) =
        (TubePolynomial.polynomial (CompactSource.polynomial (source c))
          (activeSet (TubeIndexed.arity (source c)) (active c))).map
          ((algebraMap ℝ L).comp (TubePolynomial.coefficientMap epsilon delta alpha)) := by
      unfold TubeRegularFiber.specializedPolynomial
      rw [hc]
      rfl
    rw [he, hv]
    exact h
end LeanCanny.ETR.TubeCompiledAffineRoots

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra Geometry TubeEncoding TubeProjectionEncoding
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem lowestProjectionPolynomial_eval_eq_zero_of_finite_extended_critical
    (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) →
      (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (hb : TubeRegularFiber.direction (source c)
      (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon) (TubePolynomial.base _) = 1)
    (hf : {z : Option (TubeSource.Coordinate (source c)) → K | ∀ j, MvPolynomial.aeval z
      (GenericProjectionFinite.equation
        (TubeRegularFiber.specializedPolynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon))
        (TubePolynomial.base _) (TubeRegularFiber.direction (source c)
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)) j) = 0}.Finite)
    (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (hz : z ∈ MvPolynomial.zeroLocus K (ProjectiveNullstellensatz.generated
      (finiteSystem source active n d ell c epsilon))) :
    Polynomial.eval (z (finiteParameterIndex (source c)))
      (lowestProjectionPolynomial source active n d ell c epsilon) = 0 :=
  lowestProjectionPolynomial_eval_eq_zero_of_finite_fiber source active n d ell c epsilon
    (TubeCompiledAffineRoots.finite_fiber_of_finite_extended_critical source active n d ell c epsilon hd hb hf) z hz
end LeanCanny.ETR.TubeCharacteristicQuotient
