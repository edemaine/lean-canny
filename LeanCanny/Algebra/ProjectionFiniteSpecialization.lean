/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericProjectionFinite
public import LeanCanny.Algebra.FiniteFiberSpecialization
public import LeanCanny.Algebra.PolynomialGridAvoidance

/-! # A polynomial exceptional set for normalized projection directions

Use the non-base direction coordinates as polynomial parameters. Their
fraction-field images are algebraically independent. Generic coordinate
algebraicity and denominator clearing therefore give a nonzero parameter
polynomial outside whose zero set the extended projection fibers are finite.
No bound on that exceptional polynomial is supplied.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionFiniteSpecialization
open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K ι : Type*} [Field K]

abbrev DirectionIndex (base : ι) := {i : ι // i ≠ base}
abbrev ParameterRing (K : Type*) [Field K] (base : ι) := MvPolynomial (DirectionIndex base) K
abbrev DirectionField (K : Type*) [Field K] (base : ι) := FractionRing (ParameterRing K base)

noncomputable def normalizedDirection {L : Type*} [One L] (base : ι) (u : DirectionIndex base → L) : ι → L := by
  classical
  exact fun i => if hi : i = base then 1 else u ⟨i, hi⟩

noncomputable def parameterDirection (base : ι) : ι → ParameterRing K base := by
  classical
  exact fun i => if hi : i = base then 1 else X ⟨i, hi⟩

theorem parameterDirection_base (base : ι) : parameterDirection (K := K) base base = 1 := by
  classical
  simp [parameterDirection]

theorem parameterDirection_other (base : ι) (i : DirectionIndex base) :
    parameterDirection (K := K) base i = X i := by
  classical
  simp [parameterDirection, i.property]

noncomputable def genericDirection (base : ι) : ι → DirectionField K base :=
  fun i => algebraMap (ParameterRing K base) _ (parameterDirection base i)

theorem genericDirection_base (base : ι) : genericDirection (K := K) base base = 1 := by
  rw [genericDirection, parameterDirection_base, map_one]

theorem independent_genericDirection (base : ι) :
    AlgebraicIndependent K (fun i : DirectionIndex base => genericDirection (K := K) base i) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom K (ParameterRing K base) (DirectionField K base)) :=
    IsFractionRing.injective (ParameterRing K base) (DirectionField K base)
  have h := (MvPolynomial.algebraicIndependent_X (DirectionIndex base) K).map hinj.injOn
  simpa only [IsScalarTower.coe_toAlgHom', genericDirection, parameterDirection_other, Function.comp_def] using h

section ChangeCoefficients
variable {B C : Type*} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C] [Algebra B C]
  [IsScalarTower K B C]

theorem map_liftPolynomial (p : MvPolynomial ι K) :
    (GenericProjectionFinite.liftPolynomial (B := B) p).map (algebraMap B C) =
      GenericProjectionFinite.liftPolynomial (B := C) p := by
  rw [GenericProjectionFinite.liftPolynomial, map_rename, map_map, ← IsScalarTower.algebraMap_eq K B C]
  rfl

theorem map_equation (p : MvPolynomial ι K) (base : ι) (v : ι → B) (j : Sum Bool ι) :
    (GenericProjectionFinite.equation p base v j).map (algebraMap B C) =
      GenericProjectionFinite.equation p base (fun i => algebraMap B C (v i)) j := by
  rcases j with b | i
  · cases b <;> simp only [GenericProjectionFinite.equation, map_sub, map_mul, map_X, map_one, map_liftPolynomial]
  · simp only [GenericProjectionFinite.equation, map_sub, map_mul, map_C, map_liftPolynomial]

end ChangeCoefficients

section ChangeByHom
variable {B C : Type*} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]

theorem map_liftPolynomial_of_comp (φ : B →+* C) (hφ : φ.comp (algebraMap K B) = algebraMap K C)
    (p : MvPolynomial ι K) :
    (GenericProjectionFinite.liftPolynomial (B := B) p).map φ =
      GenericProjectionFinite.liftPolynomial (B := C) p := by
  rw [GenericProjectionFinite.liftPolynomial, map_rename, map_map, hφ]
  rfl

theorem map_equation_of_comp (φ : B →+* C) (hφ : φ.comp (algebraMap K B) = algebraMap K C)
    (p : MvPolynomial ι K) (base : ι) (v : ι → B) (j : Sum Bool ι) :
    (GenericProjectionFinite.equation p base v j).map φ =
      GenericProjectionFinite.equation p base (fun i => φ (v i)) j := by
  rcases j with b | i
  · cases b <;> simp only [GenericProjectionFinite.equation, map_sub, map_mul, map_X, map_one,
      map_liftPolynomial_of_comp φ hφ]
  · simp only [GenericProjectionFinite.equation, map_sub, map_mul, map_C, map_liftPolynomial_of_comp φ hφ]

end ChangeByHom

theorem eval_parameterDirection {L : Type*} [Field L] [Algebra K L]
    (base : ι) (u : DirectionIndex base → L) (i : ι) :
    MvPolynomial.eval₂ (algebraMap K L) u (parameterDirection (K := K) base i) = normalizedDirection base u i := by
  classical
  by_cases hi : i = base <;> simp [parameterDirection, normalizedDirection, hi]

theorem eval_equation {L : Type*} [Field L] [Algebra K L] (p : MvPolynomial ι K)
    (base : ι) (u : DirectionIndex base → L) (z : Option ι → L) (j : Sum Bool ι) :
    (GenericProjectionFinite.equation p base (parameterDirection (K := K) base) j).eval₂
      (MvPolynomial.eval₂Hom (algebraMap K L) u) z =
        MvPolynomial.aeval z (GenericProjectionFinite.equation p base (normalizedDirection base u) j) := by
  let φ := MvPolynomial.eval₂Hom (algebraMap K L) u
  have hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K L := by
    ext k
    simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, φ, eval₂Hom_C]
  have hd : (fun i => φ (parameterDirection (K := K) base i)) = normalizedDirection base u := by
    funext i
    exact eval_parameterDirection base u i
  have he := map_equation_of_comp φ hφ p base (parameterDirection (K := K) base) j
  rw [hd] at he
  rw [← he, MvPolynomial.aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]

universe uL

theorem exists_finite_specialization_polynomial [CharZero K] [Fintype ι]
    (p : MvPolynomial ι K) (base : ι) :
    ∃ d : ParameterRing K base, d ≠ 0 ∧ ∀ (L : Type uL) [Field L] (φ : ParameterRing K base →+* L), φ d ≠ 0 →
      {z : Option ι → L | ∀ j,
        (GenericProjectionFinite.equation p base (parameterDirection base) j).eval₂ φ z = 0}.Finite := by
  let A := ParameterRing K base
  let F := DirectionField K base
  let I := GenericProjectionFinite.ideal p base (parameterDirection (K := K) base)
  have hcoords : ∀ P ∈ (I.map (algebraMap (MvPolynomial (Option ι) A) (MvPolynomial (Option ι) F))).minimalPrimes,
      ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i) := by
    intro P hP
    let : P.IsPrime := hP.isPrime
    let z := FiniteAlgebraicZeros.quotientPoint P
    have hz : ∀ j, MvPolynomial.aeval z (GenericProjectionFinite.equation p base (genericDirection (K := K) base) j) = 0 := by
      intro j
      have he : algebraMap (MvPolynomial (Option ι) A) (MvPolynomial (Option ι) F)
          (GenericProjectionFinite.equation p base (parameterDirection (K := K) base) j) =
            GenericProjectionFinite.equation p base (genericDirection (K := K) base) j := by
        rw [MvPolynomial.algebraMap_def, map_equation]
        rfl
      rw [FiniteAlgebraicZeros.eval_quotientPoint]
      have hmem : GenericProjectionFinite.equation p base (genericDirection (K := K) base) j ∈ P := by
        rw [← he]
        exact hP.le (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self j)))
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    exact GenericProjectionFinite.algebraic_extended_coordinates p base (genericDirection (K := K) base) z
      (genericDirection_base base) (independent_genericDirection base) hz
  obtain ⟨d, hd, hfinite⟩ := FiniteFiberSpecialization.exists_finite_specialization_certificate I hcoords
  refine ⟨d, hd, ?_⟩
  intro L _ φ hφ
  apply (hfinite L φ hφ).subset
  intro z hz
  have hI : I ≤ RingHom.ker (MvPolynomial.eval₂Hom φ z) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hz j
  exact fun q hq => hI hq

theorem exists_exceptional_polynomial [CharZero K] [Fintype ι] (p : MvPolynomial ι K) (base : ι) :
    ∃ d : ParameterRing K base, d ≠ 0 ∧ ∀ (L : Type uL) [Field L] [Algebra K L]
      (u : DirectionIndex base → L), MvPolynomial.eval₂ (algebraMap K L) u d ≠ 0 →
        {z : Option ι → L | ∀ j, MvPolynomial.aeval z
          (GenericProjectionFinite.equation p base (normalizedDirection base u) j) = 0}.Finite := by
  obtain ⟨d, hd, hfinite⟩ := exists_finite_specialization_polynomial p base
  refine ⟨d, hd, ?_⟩
  intro L _ _ u hu
  apply (hfinite L (MvPolynomial.eval₂Hom (algebraMap K L) u) hu).subset
  intro z hz j
  rw [eval_equation]
  exact hz j

theorem exists_nat_finite_extended_fiber [CharZero K] [Fintype ι] (p : MvPolynomial ι K) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      {z : Option ι → K | ∀ j, MvPolynomial.aeval z
        (GenericProjectionFinite.equation p base (normalizedDirection base (fun i => (u i : K))) j) = 0}.Finite := by
  obtain ⟨d, hd, hfinite⟩ := exists_exceptional_polynomial p base
  obtain ⟨u, hu, he⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero d hd d.totalDegree le_rfl
  refine ⟨d.totalDegree, u, hu, ?_⟩
  apply hfinite K (fun i => (u i : K))
  exact he

end LeanCanny.Algebra.ProjectionFiniteSpecialization
