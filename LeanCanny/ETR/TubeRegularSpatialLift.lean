/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularFiber
public import LeanCanny.Geometry.FiniteProjectionRoots

/-! # The reciprocal lift of a geometric projection root

A nonzero base derivative supplies the reciprocal coordinate required by
the regular spatial system. At a real projection root, regularity of the
hypersurface and normalization of the direction imply this nonvanishing.
No nonsingularity of the full critical system is assumed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularFiber
open LeanCanny.Algebra MvPolynomial
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
variable {K : Type*} [Field K]

noncomputable def reciprocalPoint (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K) :
    Option (TubeSource.Coordinate bits) → K :=
  fun i => i.elim ((pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂
    (coefficientMap bits φ) x)⁻¹ x

@[simp] theorem reciprocalPoint_some (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K)
    (i : TubeSource.Coordinate bits) : reciprocalPoint bits s φ x (some i) = x i := rfl

theorem spatial_roots_of_projection (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K)
    (hprojection : ∀ j, (TubeSource.projectionSystem bits s j).eval₂ (coefficientMap bits φ)
      (Sum.elim x (direction bits φ)) = 0)
    (hne : (pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂
      (coefficientMap bits φ) x ≠ 0) :
    ∀ j, (TubeRegularMacaulay.spatial bits s j).eval₂ φ
      (fun i => i.elim 1 (reciprocalPoint bits s φ x)) = 0 := by
  have hp : ∀ j, (TubeSource.integerProjection bits s j).eval₂ (Int.castRingHom K)
      (TubeMacaulay.values _ φ x) = 0 := by
    intro j
    exact (eval_flatten_values bits φ x (TubeSource.projectionSystem bits s j)).trans (hprojection j)
  have hreg : TubeRegularSource.RegularRoot bits s (Int.castRingHom K) (TubeMacaulay.values _ φ x) :=
    ⟨hp, fun hz => hne ((eval_base_derivative bits s φ x).symm.trans hz)⟩
  have hlift := (TubeRegularSource.root_iff bits s (Int.castRingHom K)
    (TubeMacaulay.values _ φ x)
    ((pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂ (coefficientMap bits φ) x)⁻¹).mpr
    ⟨hreg, congrArg Inv.inv (eval_base_derivative bits s φ x).symm⟩
  intro j
  exact (TubeRegularMacaulay.spatial_eval_chart bits s j φ (reciprocalPoint bits s φ x)).trans (hlift j)

theorem projection_roots_of_spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K)
    (z : Option (TubeSource.Coordinate bits) → K)
    (hz : ∀ j, (TubeRegularMacaulay.spatial bits s j).eval₂ φ (fun i => i.elim 1 z) = 0) :
    ∀ j, (TubeSource.projectionSystem bits s j).eval₂ (coefficientMap bits φ)
      (Sum.elim (fun i => z (some i)) (direction bits φ)) = 0 := by
  have hs (j : TubeRegularSource.Index bits) :=
    (TubeRegularMacaulay.spatial_eval_chart bits s j φ z).symm.trans (hz j)
  have hr := (TubeRegularSource.root_iff bits s (Int.castRingHom K)
    (TubeMacaulay.values _ φ (fun i => z (some i))) (z none)).mp hs
  intro j
  exact (eval_flatten_values bits φ (fun i => z (some i)) (TubeSource.projectionSystem bits s j)).symm.trans (hr.1.1 j)

theorem spatial_roots_of_regular_projection (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* ℝ) (x : TubeSource.Coordinate bits → ℝ)
    (hb : direction bits φ (TubePolynomial.base _) = 1)
    (hprojection : ∀ j, (TubeSource.projectionSystem bits s j).eval₂ (coefficientMap bits φ)
      (Sum.elim x (direction bits φ)) = 0)
    (hregular : Function.Surjective
      (fderiv ℝ (fun y => (TubeSource.polynomial bits s).eval₂ (coefficientMap bits φ) y) x)) :
    ∀ j, (TubeRegularMacaulay.spatial bits s j).eval₂ φ
      (fun i => i.elim 1 (reciprocalPoint bits s φ x)) = 0 := by
  have h := (ProjectionCritical.system_roots_iff (coefficientMap bits φ) (TubeSource.polynomial bits s)
    (TubePolynomial.base _) x (direction bits φ) hb).mp hprojection
  exact spatial_roots_of_projection bits s φ x hprojection
    (ProjectionCritical.base_partial_ne_zero _ _ _ _ _ h.2 hregular)

end LeanCanny.ETR.TubeRegularFiber
