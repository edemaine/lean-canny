/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelTuple
public import LeanCanny.ETR.TubeLevelFiniteFiber

/-! # One stored rational packet with finite fibers throughout a level interval

For fixed rational epsilon and delta, one packet stores a nearby normalized
rational direction whose compiled affine fibers are finite for all active
sets throughout a common positive alpha interval, over every real extension
field. There are no denominator, parameter-identity, or finiteness hypotheses
on the resulting packet. Its size and the interval are qualitative here.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open Set MvPolynomial
open scoped Classical Topology
universe uL
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

private theorem map_normalizedDirection {ι K L : Type*} [CommRing K] [CommRing L]
    (base : ι) (u : ProjectionFiniteSpecialization.DirectionIndex base → K) (φ : K →+* L) :
    (fun i => φ (ProjectionFiniteSpecialization.normalizedDirection base u i)) =
      ProjectionFiniteSpecialization.normalizedDirection base (fun i => φ (u i)) := by
  funext i
  by_cases h : i = base
  · subst i
    simp [ProjectionFiniteSpecialization.normalizedDirection]
  · simp [ProjectionFiniteSpecialization.normalizedDirection, h]

theorem exists_uniform_finite_packet (bits : List Bool) (eps del : ℚ)
    (v : TubeSource.Coordinate bits → ℝ) (hv : v (TubePolynomial.base _) = 1)
    (U : Set (TubeSource.Coordinate bits → ℝ)) (hU : U ∈ nhds v) :
    ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
      (fun i : TubeSource.Coordinate bits => (rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val : ℝ)) ∈ U ∧
      direction c (TubePolynomial.base _) = 1 ∧ ∃ a : ℝ, 0 < a ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < a → ∀ (L : Type uL) [Field L] [Algebra ℝ L],
          ∀ (active : List Bool → List Bool) (ell : List Bool → ℕ → ℤ),
            (zeroLocus L (ProjectiveNullstellensatz.generated
              (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator ell c (algebraMap ℝ L alpha)))).Finite := by
  classical
  obtain ⟨u, hu, a, ha, hf⟩ := TubePolynomial.exists_uniform_rational_finite_extended_direction_near
    (CompactSource.polynomial bits) (eps : ℝ) (del : ℝ) v hv U hU
  let w : TubeSource.Coordinate bits → ℚ := ProjectionFiniteSpecialization.normalizedDirection (TubePolynomial.base _) u
  have hw : w (TubePolynomial.base _) = 1 := dite_eq_left rfl
  have hwReal : (fun i => (w i : ℝ)) = ProjectionCritical.rationalDirection (TubePolynomial.base _) u :=
    map_normalizedDirection _ u (Rat.castHom ℝ)
  obtain ⟨c, hc, he, hd, hr⟩ := exists_packet_parameters bits eps del w
  have hnear : (fun i : TubeSource.Coordinate bits => (rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val : ℝ)) ∈ U := by
    have heq : (fun i : TubeSource.Coordinate bits => (rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val : ℝ)) =
        ProjectionCritical.rationalDirection (TubePolynomial.base _) u :=
      (funext (fun i => congrArg (fun q : ℚ => (q : ℝ)) (hr i))).trans hwReal
    rw [heq]
    exact hu
  subst bits
  have hdir : direction c = w := funext hr
  have hb : direction c (TubePolynomial.base _) = 1 := (congrFun hdir _).trans hw
  refine ⟨c, rfl, he, hd, hnear, hb, a, ha, ?_⟩
  intro alpha hp hl L _ _ active ell
  apply finite_fiber_of_finite_extended_critical active ell c alpha hb
  have hvL : (fun i => algebraMap ℝ L (direction c i : ℝ)) =
      ProjectionFiniteSpecialization.normalizedDirection (TubePolynomial.base _)
        (fun i => algebraMap ℝ L (u i : ℝ)) := by
    have h := map_normalizedDirection (TubePolynomial.base _) u ((algebraMap ℝ L).comp (Rat.castHom ℝ))
    exact (congrArg (fun d => fun i => algebraMap ℝ L (d i : ℝ)) hdir).trans h
  rw [he, hd, hvL]
  exact hf alpha hp hl L (activeSet (TubeIndexed.arity (pairFst c)) (active c))
end LeanCanny.ETR.TubeLevelPacket
