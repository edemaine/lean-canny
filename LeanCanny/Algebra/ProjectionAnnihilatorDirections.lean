/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateAnnihilatorSpecialization
public import LeanCanny.Algebra.ProjectionSystemCoordinates

/-! # Integer projection directions retaining coordinate annihilators

A direction carries the cleared annihilator certificate and its nonvanishing
specialization. Every solution of its extended critical equations has algebraic
coordinates over the input field in every extension field. Integer grids give
such directions, simultaneously for finite families of surfaces. The grid
bound still depends on existential certificate polynomials.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionAnnihilatorDirections
open MvPolynomial ProjectionFiniteSpecialization

variable {K ι : Type*} [Field K]

noncomputable def coefficientMap (base : ι) (u : DirectionIndex base → ℕ) : ParameterRing K base →+* K :=
  MvPolynomial.eval (fun i => (u i : K))

structure CertifiedDirection (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ) [Fintype ι] where
  certificate : CoordinateAnnihilatorSpecialization.Certificate
    (GenericProjectionFinite.ideal p base (parameterDirection (K := K) base))
  avoids : coefficientMap base u certificate.exceptional ≠ 0

theorem map_parameter_equation (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ) (j : Sum Bool ι) :
    (GenericProjectionFinite.equation p base (parameterDirection (K := K) base) j).map (coefficientMap base u) =
      ProjectionSystemCoordinates.equations p base u j := by
  have hφ : (coefficientMap (K := K) base u).comp (algebraMap K (ParameterRing K base)) = algebraMap K K := by
    ext a
    simp [coefficientMap, MvPolynomial.algebraMap_eq]
  rw [ProjectionFiniteSpecialization.map_equation_of_comp _ hφ]
  have hd : (fun i => coefficientMap (K := K) base u (parameterDirection base i)) =
      normalizedDirection base (fun i => (u i : K)) := by
    funext i
    simpa only [coefficientMap, MvPolynomial.eval₂_id, Algebra.algebraMap_self] using
      eval_parameterDirection (K := K) base (fun i => (u i : K)) i
  rw [hd]
  rfl

section Extension
variable {E : Type*} [Field E] [Algebra K E]

private theorem ideal_solution (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (z : Option ι → E) (hz : z ∈ FiniteSystemCoordinates.zeroSet (L := E) (ProjectionSystemCoordinates.equations p base u)) :
    ∀ q ∈ GenericProjectionFinite.ideal p base (parameterDirection (K := K) base),
      q.eval₂ ((algebraMap K E).comp (coefficientMap base u)) z = 0 := by
  have hI : GenericProjectionFinite.ideal p base (parameterDirection (K := K) base) ≤
      RingHom.ker (MvPolynomial.eval₂Hom ((algebraMap K E).comp (coefficientMap base u)) z) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change MvPolynomial.eval₂ ((algebraMap K E).comp (coefficientMap base u)) z _ = 0
    rw [← MvPolynomial.eval₂_map, map_parameter_equation]
    exact hz j
  exact fun q hq => hI hq

namespace CertifiedDirection
variable [Fintype ι] {p : MvPolynomial ι K} {base : ι} {u : DirectionIndex base → ℕ}

theorem algebraic_coordinates (c : CertifiedDirection p base u) (z : Option ι → E)
    (hz : z ∈ FiniteSystemCoordinates.zeroSet (L := E) (ProjectionSystemCoordinates.equations p base u)) :
    ∀ j, IsAlgebraic K (z j) :=
  c.certificate.algebraic_coordinates (coefficientMap base u) c.avoids z (ideal_solution p base u z hz)

theorem finite_solutions (c : CertifiedDirection p base u) :
    (FiniteSystemCoordinates.zeroSet (L := E) (ProjectionSystemCoordinates.equations p base u)).Finite := by
  apply (c.certificate.finite_solutions (E := E) (coefficientMap base u) c.avoids).subset
  exact fun z hz => ideal_solution p base u z hz

theorem nonempty_representation [CharZero K] (c : CertifiedDirection p base u) :
    Nonempty (FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (ProjectionSystemCoordinates.equations p base u)) :=
  FiniteSystemCoordinates.nonempty_algebraicClosure_representation _ (c.finite_solutions (E := AlgebraicClosure K))

end CertifiedDirection
end Extension

theorem exists_certified_direction [Fintype ι] [CharZero K] (p : MvPolynomial ι K) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧ Nonempty (CertifiedDirection p base u) := by
  obtain ⟨c⟩ := CoordinateAnnihilatorSpecialization.nonempty_certificate
    (GenericProjectionFinite.ideal p base (parameterDirection (K := K) base))
    (ProjectionFiniteSpecialization.generic_quotient_coordinates_algebraic p base)
  obtain ⟨u, hu, he⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero c.exceptional c.exceptional_ne_zero
    c.exceptional.totalDegree le_rfl
  exact ⟨c.exceptional.totalDegree, u, hu, ⟨⟨c, he⟩⟩⟩

theorem exists_family_certified_directions [Fintype ι] [CharZero K]
    {σ : Type*} [Fintype σ] (p : σ → MvPolynomial ι K) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧ ∀ r, Nonempty (CertifiedDirection (p r) base u) := by
  classical
  have h (r : σ) := CoordinateAnnihilatorSpecialization.nonempty_certificate
    (GenericProjectionFinite.ideal (p r) base (parameterDirection (K := K) base))
    (ProjectionFiniteSpecialization.generic_quotient_coordinates_algebraic (p r) base)
  let c := fun r => Classical.choice (h r)
  obtain ⟨u, hu, he⟩ := PolynomialGridAvoidance.exists_nat_common_nonzero
    (fun r => (c r).exceptional) (fun r => (c r).exceptional_ne_zero)
    (∑ r, (c r).exceptional.totalDegree) le_rfl
  exact ⟨∑ r, (c r).exceptional.totalDegree, u, hu, fun r => ⟨⟨c r, he r⟩⟩⟩

end LeanCanny.Algebra.ProjectionAnnihilatorDirections
