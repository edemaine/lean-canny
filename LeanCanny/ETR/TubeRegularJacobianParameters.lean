/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularJacobianGeneric
public import Mathlib.Algebra.CharZero.Infinite

/-! # Generic level and direction parameters for the actual tube determinant -/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularJacobianParameters
open LeanCanny.Algebra Geometry MvPolynomial
open TubeEncoding TubeProjectionEncoding
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

section Energy
variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
theorem map_spatial (p : MvPolynomial ι ℤ)
    (φ ψ : TubePolynomial.Coefficient →+* R) :
    (TubePolynomial.spatial p).map φ = (TubePolynomial.spatial p).map ψ := by
  simp only [TubePolynomial.spatial, MvPolynomial.map_rename, MvPolynomial.map_map]
  rw [show φ.comp (Int.castRingHom TubePolynomial.Coefficient) =
    ψ.comp (Int.castRingHom TubePolynomial.Coefficient) from Subsingleton.elim _ _]

omit [Fintype ι] in
theorem map_constraint (p : MvPolynomial ι ℤ)
    (φ ψ : TubePolynomial.Coefficient →+* R)
    (he : φ (X (some false)) = ψ (X (some false)))
    (i : PolynomialPerturbation.Constraint ι) :
    (TubePolynomial.constraint p i).map φ = (TubePolynomial.constraint p i).map ψ := by
  rcases i with b | ⟨i, b⟩ <;> cases b <;>
    simp only [TubePolynomial.constraint, map_add, map_sub, map_neg, map_one,
      MvPolynomial.map_X, MvPolynomial.map_C, he, map_spatial p φ ψ]

theorem map_energy (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι))
    (φ ψ : TubePolynomial.Coefficient →+* R)
    (he : φ (X (some false)) = ψ (X (some false)))
    (hd : φ (X (some true)) = ψ (X (some true))) :
    (TubePolynomial.energy p s).map φ = (TubePolynomial.energy p s).map ψ := by
  simp only [TubePolynomial.energy, TubePolynomial.radius, map_add, map_sub,
    map_pow, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, hd,
    map_constraint p φ ψ he]

end Energy

section Generic
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def coefficient (epsilon delta alpha : K) : TubePolynomial.Coefficient →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K)
    (fun p => p.elim alpha (fun b => if b then delta else epsilon))

@[simp] theorem coefficient_alpha (epsilon delta alpha : K) :
    coefficient epsilon delta alpha (X none) = alpha := by
  rw [coefficient, MvPolynomial.eval₂Hom_X']
  rfl

@[simp] theorem coefficient_epsilon (epsilon delta alpha : K) :
    coefficient epsilon delta alpha (X (some false)) = epsilon := by
  rw [coefficient, MvPolynomial.eval₂Hom_X']
  rfl

@[simp] theorem coefficient_delta (epsilon delta alpha : K) :
    coefficient epsilon delta alpha (X (some true)) = delta := by
  rw [coefficient, MvPolynomial.eval₂Hom_X']
  rfl

noncomputable def energy (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : K) : MvPolynomial (TubeSource.Coordinate bits) K :=
  (TubePolynomial.energy (CompactSource.polynomial bits) s).map (coefficient epsilon delta 0)

noncomputable def parameterMap (bits : List Bool) (epsilon delta : K)
    (alpha : L) (v : TubeSource.Coordinate bits → L) :
    TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L :=
  MvPolynomial.eval₂Hom (Int.castRingHom L)
    (Sum.elim v (fun p => p.elim alpha (fun b =>
      if b then algebraMap K L delta else algebraMap K L epsilon)))

theorem direction_parameterMap (bits : List Bool) (epsilon delta : K)
    (alpha : L) (v : TubeSource.Coordinate bits → L) :
    TubeRegularFiber.direction bits (parameterMap bits epsilon delta alpha v) = v := by
  funext i
  change (parameterMap bits epsilon delta alpha v) (X (.inl i)) = v i
  rw [parameterMap, MvPolynomial.eval₂Hom_X']
  rfl

theorem coefficientMap_parameterMap (bits : List Bool) (epsilon delta : K)
    (alpha : L) (v : TubeSource.Coordinate bits → L) :
    TubeRegularFiber.coefficientMap bits (parameterMap bits epsilon delta alpha v) =
      coefficient (algebraMap K L epsilon) (algebraMap K L delta) alpha := by
  apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
  intro p
  rw [TubeRegularFiber.coefficientMap, MvPolynomial.eval₂Hom_X', parameterMap,
    MvPolynomial.eval₂Hom_X', coefficient, MvPolynomial.eval₂Hom_X']
  rfl

theorem specialized_parameterMap (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : K) (alpha : L) (v : TubeSource.Coordinate bits → L) :
    TubeRegularFiber.specializedPolynomial bits s (parameterMap bits epsilon delta alpha v) =
      (energy bits s epsilon delta).map (algebraMap K L) - C alpha := by
  rw [TubeRegularFiber.specializedPolynomial, coefficientMap_parameterMap]
  change (TubePolynomial.energy (CompactSource.polynomial bits) s - C (X none)).map _ = _
  rw [map_sub, MvPolynomial.map_C, coefficient_alpha]
  congr 1
  rw [energy, MvPolynomial.map_map]
  apply map_energy
  · rw [coefficient_epsilon, RingHom.comp_apply, coefficient_epsilon]
  · rw [coefficient_delta, RingHom.comp_apply, coefficient_delta]

end Generic

section GenericField
open LevelProjectionSpecialization
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def genericMap (bits : List Bool) (epsilon delta : K)
    [Algebra (ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))) L] :
    TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L :=
  parameterMap bits epsilon delta
    (algebraMap (ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))) L (genericLevel (K := K) (TubePolynomial.base _)))
    (fun i => algebraMap (ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))) L
      (genericDirection (K := K) (TubePolynomial.base _) i))

/-- The actual native integer tube determinant has no zero at a generic regular
root, in every field extension of the joint level/direction parameter field. -/
theorem generic_determinant_ne_zero [CharZero K]
    (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (epsilon delta : K)
    [Algebra (ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))) L]
    [IsScalarTower K (ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))) L]
    (z : Option (TubeSource.Coordinate bits) → L)
    (hz : ∀ i, (TubeRegularSource.polynomial bits s i).eval₂ (Int.castRingHom L)
      (TubeRegularJacobianGeneric.nativeAssignment bits (genericMap (L := L) bits epsilon delta) z) = 0) :
    (TubeRegularJacobianBudget.polynomial bits s).eval₂ (Int.castRingHom L)
      (TubeRegularJacobianGeneric.nativeAssignment bits (genericMap (L := L) bits epsilon delta) z) ≠ 0 := by
  have : CharZero L := Algebra.charZero_of_charZero K L
  let F := ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))
  let alpha : L := algebraMap F L (genericLevel (K := K) (TubePolynomial.base _))
  let v : TubeSource.Coordinate bits → L := fun i =>
    algebraMap F L (genericDirection (K := K) (TubePolynomial.base _) i)
  have hind : AlgebraicIndependent K (GenericProjectionJacobian.parameters (TubePolynomial.base _) alpha v) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom K F L) := (algebraMap F L).injective
    have h := (GenericProjectionJacobian.generic_parameters_independent
      (K := K) (TubePolynomial.base (Fin (CompactSource.term bits).arity))).map hinj.injOn
    convert h using 1
    funext i
    by_cases hi : i = TubePolynomial.base _ <;>
      simp [GenericProjectionJacobian.parameters, hi, alpha, v] <;> rfl
  have hb : v (TubePolynomial.base _) = 1 := by
    change algebraMap F L (genericDirection (K := K) (TubePolynomial.base _) (TubePolynomial.base _)) = 1
    rw [genericDirection, parameterDirection_base, map_one, map_one]
  have hd := direction_parameterMap bits epsilon delta alpha v
  have hp := specialized_parameterMap bits s epsilon delta alpha v
  change TubeRegularFiber.direction bits (genericMap (L := L) bits epsilon delta) = v at hd
  change TubeRegularFiber.specializedPolynomial bits s (genericMap (L := L) bits epsilon delta) =
    (energy bits s epsilon delta).map (algebraMap K L) - C alpha at hp
  apply TubeRegularJacobianGeneric.determinant_ne_zero_of_independent bits s
    (genericMap (L := L) bits epsilon delta) (energy bits s epsilon delta) alpha hp
  · rw [hd]
    exact hb
  · rw [hd]
    exact hind
  · exact hz

end GenericField

end LeanCanny.ETR.TubeRegularJacobianParameters
