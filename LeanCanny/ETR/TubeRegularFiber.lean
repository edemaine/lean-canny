/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularMacaulay
public import LeanCanny.Algebra.GenericProjectionFinite

/-! # From the actual regular tube rows to finite critical fibers

Specializing the coefficient parameters in the partially homogenized tube
system recovers the extended critical equations of the specialized tube
polynomial. The reciprocal coordinate enforces a nonzero base derivative.
A normalized direction with a finite extended critical fiber therefore gives
a finite spatial root set, over every field.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularFiber
open LeanCanny.Algebra MvPolynomial
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
variable {K : Type*} [Field K]

noncomputable def coefficientMap (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) : TubePolynomial.Coefficient →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K) (fun p => φ (X (.inr p)))

noncomputable def direction (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) : TubeSource.Coordinate bits → K :=
  fun i => φ (X (.inl i))

noncomputable def specializedPolynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) : MvPolynomial (TubeSource.Coordinate bits) K :=
  (TubeSource.polynomial bits s).map (coefficientMap bits φ)

theorem eval_flatten_values (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K)
    (p : MvPolynomial (Sum (TubeSource.Coordinate bits) (TubeSource.Coordinate bits)) TubePolynomial.Coefficient) :
    (NestedPolynomial.flatten p).eval₂ (Int.castRingHom K) (TubeMacaulay.values _ φ x) =
      p.eval₂ (coefficientMap bits φ) (Sum.elim x (direction bits φ)) :=
  NestedPolynomial.eval_flatten _ _ _ p

theorem eval_level (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K) :
    (TubeSource.integerProjection bits s none).eval₂ (Int.castRingHom K) (TubeMacaulay.values _ φ x) =
      (TubeSource.polynomial bits s).eval₂ (coefficientMap bits φ) x := by
  change (NestedPolynomial.flatten (ProjectionEquations.polynomial (TubeSource.polynomial bits s)
    (TubePolynomial.base _) none)).eval₂ (Int.castRingHom K) _ = _
  exact (eval_flatten_values bits φ x _).trans (ProjectionEquations.eval_level _ _ _ _ _)

theorem eval_partial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K)
    (i : {i : TubeSource.Coordinate bits // i ≠ TubePolynomial.base _}) :
    (TubeSource.integerProjection bits s (some i)).eval₂ (Int.castRingHom K) (TubeMacaulay.values _ φ x) =
      (pderiv i.val (TubeSource.polynomial bits s)).eval₂ (coefficientMap bits φ) x -
        direction bits φ i.val * (pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂ (coefficientMap bits φ) x := by
  change (NestedPolynomial.flatten (ProjectionEquations.polynomial (TubeSource.polynomial bits s)
    (TubePolynomial.base _) (some i.val))).eval₂ (Int.castRingHom K) _ = _
  exact (eval_flatten_values bits φ x _).trans (ProjectionEquations.eval_partial _ _ _ _ _ _)

theorem eval_base_derivative (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K) :
    (pderiv (TubeRegularSource.base (TubeIndexed.arity bits)) (TubeSource.integerProjection bits s none)).eval₂
      (Int.castRingHom K) (TubeMacaulay.values _ φ x) =
      (pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂ (coefficientMap bits φ) x := by
  change (pderiv (.inl (.inl (TubePolynomial.base _)))
    (NestedPolynomial.flatten (rename Sum.inl (TubeSource.polynomial bits s)))).eval₂ (Int.castRingHom K) _ = _
  rw [← NestedPolynomial.flatten_pderiv, pderiv_rename Sum.inl_injective]
  exact (eval_flatten_values bits φ x _).trans (MvPolynomial.eval₂_rename _ _ _ _)

theorem eval_specialized (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K) :
    aeval x (specializedPolynomial bits s φ) = (TubeSource.polynomial bits s).eval₂ (coefficientMap bits φ) x := by
  simp only [specializedPolynomial, aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem eval_specialized_partial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K) (x : TubeSource.Coordinate bits → K)
    (i : TubeSource.Coordinate bits) :
    aeval x (pderiv i (specializedPolynomial bits s φ)) =
      (pderiv i (TubeSource.polynomial bits s)).eval₂ (coefficientMap bits φ) x := by
  simp only [specializedPolynomial, MvPolynomial.pderiv_map, aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem extended_roots_of_spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K)
    (hb : direction bits φ (TubePolynomial.base _) = 1)
    (z : Option (TubeSource.Coordinate bits) → K)
    (hz : ∀ j, (TubeRegularMacaulay.spatial bits s j).eval₂ φ (fun i => i.elim 1 z) = 0) :
    ∀ j, aeval z (GenericProjectionFinite.equation (specializedPolynomial bits s φ)
      (TubePolynomial.base _) (direction bits φ) j) = 0 := by
  have hs (j : TubeRegularSource.Index bits) := (TubeRegularMacaulay.spatial_eval_chart bits s j φ z).symm.trans (hz j)
  have hr := (TubeRegularSource.root_iff bits s (Int.castRingHom K)
    (TubeMacaulay.values _ φ (fun k => z (some k))) (z none)).mp hs
  have hp := (eval_level bits s φ (fun k => z (some k))).symm.trans (hr.1.1 none)
  have hne : (pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂
      (coefficientMap bits φ) (fun k => z (some k)) ≠ 0 := by
    rw [← eval_base_derivative]
    exact hr.1.2
  have hi : z none * (pderiv (TubePolynomial.base _) (TubeSource.polynomial bits s)).eval₂
      (coefficientMap bits φ) (fun k => z (some k)) = 1 := by
    have hu := hr.2.trans (congrArg Inv.inv (eval_base_derivative bits s φ (fun k => z (some k))))
    rw [hu, inv_mul_cancel₀ hne]
  intro j
  rcases j with b | i
  · cases b
    · rw [GenericProjectionFinite.equation, GenericProjectionFinite.eval_liftPolynomial, eval_specialized]
      exact hp
    · rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_X,
        GenericProjectionFinite.eval_liftPolynomial, eval_specialized_partial, map_one]
      exact sub_eq_zero.mpr hi
  · rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_C,
      GenericProjectionFinite.eval_liftPolynomial, GenericProjectionFinite.eval_liftPolynomial,
      eval_specialized_partial, eval_specialized_partial, Algebra.algebraMap_self, RingHom.id_apply]
    by_cases he : i = TubePolynomial.base _
    · rw [he, hb, one_mul, sub_self]
    · exact (eval_partial bits s φ (fun k => z (some k)) ⟨i, he⟩).symm.trans (hr.1.1 (some ⟨i, he⟩))

theorem finite_spatial_roots_of_finite_extended (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* K)
    (hb : direction bits φ (TubePolynomial.base _) = 1)
    (hf : {z : Option (TubeSource.Coordinate bits) → K | ∀ j,
      aeval z (GenericProjectionFinite.equation (specializedPolynomial bits s φ)
        (TubePolynomial.base _) (direction bits φ) j) = 0}.Finite) :
    {z : Option (TubeSource.Coordinate bits) → K | ∀ j,
      (TubeRegularMacaulay.spatial bits s j).eval₂ φ (fun i => i.elim 1 z) = 0}.Finite :=
  hf.subset (fun z hz => extended_roots_of_spatial bits s φ hb z hz)
end LeanCanny.ETR.TubeRegularFiber
