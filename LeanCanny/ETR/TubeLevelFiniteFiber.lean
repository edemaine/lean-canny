/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelParameters
public import LeanCanny.ETR.TubeCharacteristicGeometricPersistence

/-! # Finite compiled fibers for stored rational tube parameters

The packet's proved parameter identities and positive denominators discharge
the substitution hypotheses in the geometric finiteness bridge. Only the
geometric condition on the stored normalized direction remains. Choosing a
suitable tuple with source-size bounds is a separate obligation.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

section Extension
variable {L : Type*} [Field L] [Algebra ℝ L]

theorem parameters_direction_real_extension (c : List Bool) (alpha : ℝ) :
    TubeRegularFiber.direction (pairFst c) (parameters c (algebraMap ℝ L alpha)) =
      fun i => algebraMap ℝ L (direction c i : ℝ) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℝ L).injective
  rw [parameters_direction]
  funext i
  exact (RingHom.map_rat_algebraMap (algebraMap ℝ L) (direction c i)).symm

theorem finite_fiber_of_finite_extended_critical (active : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (alpha : ℝ)
    (hb : direction c (TubePolynomial.base _) = 1)
    (hf : {z : Option (TubeSource.Coordinate (pairFst c)) → L | ∀ j, MvPolynomial.aeval z
      (GenericProjectionFinite.equation
        ((TubeSource.polynomial (pairFst c) (activeSet (TubeIndexed.arity (pairFst c)) (active c))).map
          ((algebraMap ℝ L).comp (TubePolynomial.coefficientMap (epsilon c : ℝ) (delta c : ℝ) alpha)))
        (TubePolynomial.base _) (fun i => algebraMap ℝ L (direction c i : ℝ)) j) = 0}.Finite) :
    (MvPolynomial.zeroLocus L (ProjectiveNullstellensatz.generated
      (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator ell c (algebraMap ℝ L alpha)))).Finite := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℝ L).injective
  apply TubeCompiledAffineRoots.finite_fiber_of_finite_extended_critical
    pairFst active numerator denominator ell c (algebraMap ℝ L alpha)
  · exact fun i _ => denominator_eval_ne_zero c i _
  · change TubeRegularFiber.direction (pairFst c) (parameters c (algebraMap ℝ L alpha)) (TubePolynomial.base _) = 1
    exact (congrFun (parameters_direction c (algebraMap ℝ L alpha)) (TubePolynomial.base _)).trans
      ((congrArg (algebraMap ℚ L) hb).trans (map_one _))
  · change {z : Option (TubeSource.Coordinate (pairFst c)) → L | ∀ j, MvPolynomial.aeval z
      (GenericProjectionFinite.equation
        (TubeRegularFiber.specializedPolynomial (pairFst c) (activeSet (TubeIndexed.arity (pairFst c)) (active c))
          (parameters c (algebraMap ℝ L alpha)))
        (TubePolynomial.base _) (TubeRegularFiber.direction (pairFst c)
          (parameters c (algebraMap ℝ L alpha))) j) = 0}.Finite
    have he : TubeRegularFiber.specializedPolynomial (pairFst c)
        (activeSet (TubeIndexed.arity (pairFst c)) (active c)) (parameters c (algebraMap ℝ L alpha)) =
        (TubeSource.polynomial (pairFst c) (activeSet (TubeIndexed.arity (pairFst c)) (active c))).map
          ((algebraMap ℝ L).comp (TubePolynomial.coefficientMap (epsilon c : ℝ) (delta c : ℝ) alpha)) := by
      unfold TubeRegularFiber.specializedPolynomial
      rw [parameters_coefficientMap]
    rw [he, parameters_direction_real_extension]
    exact hf
end Extension
end LeanCanny.ETR.TubeLevelPacket
