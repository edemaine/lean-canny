/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionCriticalFamily

/-! # One integer direction for an entire critical parameter family

Choose the direction over the fraction field of the original coefficient
ring. Retained generic coordinate equations and generic Jacobian regularity
clear to certificates over that original ring. One nonzero factor then makes
every retained specialization finite, nonsingular, and annihilated by nonzero
specialized coordinate polynomials. There is no input-size estimate yet.
-/

@[expose] public section

namespace LeanCanny.Algebra.UniformCriticalSpecialization
open MvPolynomial ProjectionFiniteSpecialization ProjectionCriticalFamily
attribute [local instance] MvPolynomial.algebraMvPolynomial
set_option backward.isDefEq.respectTransparency false

universe u
variable {A F ι : Type u} [CommRing A] [IsDomain A] [Field F] [CharZero F]
  [Algebra A F] [IsFractionRing A F] [Fintype ι] [DecidableEq ι]

include F in
theorem exists_uniform (q : MvPolynomial ι A) (base : ι) :
    ∃ B : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ B) ∧
      let v := normalizedDirection base (fun i => (u i : A))
      ∃ cert : CoordinateAnnihilatorSpecialization.Certificate (ideal q base v),
        ∃ r : A, r ≠ 0 ∧
          ∀ (L : Type u) [Field L] (φ : A →+* L), φ r ≠ 0 →
            (∀ i, (cert.polynomial i).map φ ≠ 0) ∧
            {z : Option ι → L | ∀ j, (equation q base v j).eval₂ φ z = 0}.Finite ∧
            ∀ z : Option ι → L, (∀ j, (equation q base v j).eval₂ φ z = 0) →
              (jacobian q base v).eval₂ φ z ≠ 0 ∧
                ∀ i, Polynomial.aeval (z i) ((cert.polynomial i).map φ) = 0 := by
  let qF := q.map (algebraMap A F)
  obtain ⟨B, u, hu, Q, hQ, hall⟩ := FixedLevelRegularSpecialization.exists_nat_regular_coordinates qF base
  let v := normalizedDirection base (fun i => (u i : A))
  let I := ideal q base v
  have hgeneric : ∀ (L : Type u) [Field L] [Algebra F L] (z : Option ι → L),
      (∀ j, aeval z ((equation q base v j).map (algebraMap A F)) = 0) →
        aeval z ((jacobian q base v).map (algebraMap A F)) ≠ 0 ∧
          ∀ i, Polynomial.aeval (z i) (Q i) = 0 := by
    intro L _ _ z hz
    have hdir : (fun i => algebraMap F L (algebraMap A F (v i))) =
        normalizedDirection base (fun i => (u i : L)) := by
      simpa only [RingHom.comp_apply] using
        map_nat_direction ((algebraMap F L).comp (algebraMap A F)) base u
    have hr := (equations_map_iff (algebraMap A F) q base v z).mp hz
    rw [hdir] at hr
    refine ⟨?_, (hall L).2.2 z hr⟩
    rw [aeval_mapped_jacobian, hdir]
    exact (hall L).2.1 z hr
  have hcoords : ∀ P ∈ (I.map (algebraMap (MvPolynomial (Option ι) A)
      (MvPolynomial (Option ι) F))).minimalPrimes,
      ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i) := by
    intro P hP
    let : P.IsPrime := hP.isPrime
    let z := FiniteAlgebraicZeros.quotientPoint P
    have hz : ∀ j, aeval z ((equation q base v j).map (algebraMap A F)) = 0 := by
      intro j
      rw [FiniteAlgebraicZeros.eval_quotientPoint]
      have hj : equation q base v j ∈ I := Ideal.subset_span (Set.mem_range_self j)
      have hm : (equation q base v j).map (algebraMap A F) ∈ P := by
        simpa only [MvPolynomial.algebraMap_def] using hP.le (Ideal.mem_map_of_mem _ hj)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
    intro i
    exact ⟨Q i, hQ i, (hgeneric _ z hz).2 i⟩
  obtain ⟨cert⟩ := CoordinateAnnihilatorSpecialization.nonempty_certificate (F := F) I hcoords
  obtain ⟨dr, hdr, hregular⟩ := RegularFiberSpecialization.exists_exceptional (F := F)
    (equation q base v) (jacobian q base v) (fun L _ _ z hz => (hgeneric L z hz).1)
  refine ⟨B, u, hu, cert, dr * cert.exceptional, mul_ne_zero hdr cert.exceptional_ne_zero, ?_⟩
  intro L _ φ hφ
  have hfac : φ dr ≠ 0 ∧ φ cert.exceptional ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [map_mul] using hφ)
  have hI (z : Option ι → L) (hz : ∀ j, (equation q base v j).eval₂ φ z = 0) :
      ∀ f ∈ I, f.eval₂ φ z = 0 := by
    have hk : I ≤ RingHom.ker (eval₂Hom φ z) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hz j
    exact fun _ hf => hk hf
  refine ⟨cert.specialized_polynomial_ne_zero φ hfac.2, ?_, ?_⟩
  · apply (cert.finite_solutions (E := L) φ hfac.2).subset
    intro z hz f hf
    simpa only [Algebra.algebraMap_self, RingHom.id_comp] using hI z hz f hf
  · intro z hz
    refine ⟨hregular L φ z hfac.1 hz, ?_⟩
    intro i
    apply cert.aeval_specialized_eq_zero φ hfac.2 z
    intro f hf
    simpa only [Algebra.algebraMap_self, RingHom.id_comp] using hI z hz f hf

end LeanCanny.Algebra.UniformCriticalSpecialization
