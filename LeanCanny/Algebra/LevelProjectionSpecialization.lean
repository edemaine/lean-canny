/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionParameterCoordinates
public import LeanCanny.Algebra.ProjectionFiniteSpecialization

/-! # A joint exceptional polynomial for levels and projection directions

Treat the level and non-base direction coordinates as independent parameters.
Direction derivations fix the level, so generic extended critical coordinates
are algebraic. Clearing denominators gives one nonzero polynomial controlling
finite fibers under simultaneous specialization of both kinds of parameters.
-/

@[expose] public section

namespace LeanCanny.Algebra.LevelProjectionSpecialization
open MvPolynomial
open ProjectionFiniteSpecialization (DirectionIndex normalizedDirection)

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K ι : Type*} [Field K]

abbrev ParameterRing (K : Type*) [Field K] (base : ι) := MvPolynomial (Option (DirectionIndex base)) K
abbrev ParameterField (K : Type*) [Field K] (base : ι) := FractionRing (ParameterRing K base)

noncomputable def levelPolynomial {B : Type*} [CommRing B] [Algebra K B]
    (p : MvPolynomial ι K) (a : B) : MvPolynomial ι B := p.map (algebraMap K B) - C a

theorem pderiv_levelPolynomial {B : Type*} [CommRing B] [Algebra K B]
    (p : MvPolynomial ι K) (a : B) (i : ι) :
    pderiv i (levelPolynomial p a) = (pderiv i p).map (algebraMap K B) := by
  simp [levelPolynomial, pderiv_map]

theorem fixed_levelPolynomial {B : Type*} [Field B] [Algebra K B]
    (D : Derivation K B B) (p : MvPolynomial ι K) (a : B) (ha : D a = 0) :
    MvCoefficientDerivation.derivation D (levelPolynomial p a) = 0 := by
  rw [levelPolynomial, map_sub, MvCoefficientChainRule.derivation_map_algebraMap,
    MvCoefficientDerivation.derivation_C, ha, map_zero, sub_zero]

noncomputable def parameterDirection (base : ι) : ι → ParameterRing K base := by
  classical
  exact fun i => if hi : i = base then 1 else X (some ⟨i, hi⟩)

theorem parameterDirection_base (base : ι) : parameterDirection (K := K) base base = 1 := by
  classical
  simp [parameterDirection]

theorem parameterDirection_other (base : ι) (i : DirectionIndex base) :
    parameterDirection (K := K) base i = X (some i) := by
  classical
  simp [parameterDirection, i.property]

noncomputable def genericDirection (base : ι) : ι → ParameterField K base :=
  fun i => algebraMap (ParameterRing K base) _ (parameterDirection base i)

noncomputable def genericLevel (base : ι) : ParameterField K base :=
  algebraMap (ParameterRing K base) _ (X none)

noncomputable def equation (p : MvPolynomial ι K) (base : ι) :
    Sum Bool ι → MvPolynomial (Option ι) (ParameterRing K base)
  | .inl false => GenericProjectionFinite.liftPolynomial (B := ParameterRing K base) p - C (X none)
  | j => GenericProjectionFinite.equation p base (parameterDirection base) j

section ChangeCoefficients
variable {B : Type*} [Field B] [Algebra K B]

theorem lift_levelPolynomial (p : MvPolynomial ι K) (a : B) :
    GenericProjectionFinite.liftPolynomial (B := B) (levelPolynomial p a) =
      GenericProjectionFinite.liftPolynomial p - C a := by
  simp [GenericProjectionFinite.liftPolynomial, levelPolynomial, Algebra.algebraMap_self, map_id]

theorem lift_pderiv_levelPolynomial (p : MvPolynomial ι K) (a : B) (i : ι) :
    GenericProjectionFinite.liftPolynomial (B := B) (pderiv i (levelPolynomial p a)) =
      GenericProjectionFinite.liftPolynomial (B := B) (pderiv i p) := by
  rw [pderiv_levelPolynomial]
  simp [GenericProjectionFinite.liftPolynomial, Algebra.algebraMap_self, map_id]

theorem map_equation (p : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B) (j : Sum Bool ι) :
    (equation p base j).map φ = GenericProjectionFinite.equation
      (levelPolynomial p (φ (X none))) base (fun i => φ (parameterDirection base i)) j := by
  rcases j with b | i
  · cases b
    · simp only [equation, GenericProjectionFinite.equation, map_sub, map_C,
        ProjectionFiniteSpecialization.map_liftPolynomial_of_comp φ hφ, lift_levelPolynomial]
    · simp only [equation, GenericProjectionFinite.equation, map_sub, map_mul, map_X, map_one,
        ProjectionFiniteSpecialization.map_liftPolynomial_of_comp φ hφ, lift_pderiv_levelPolynomial]
  · simp only [equation, GenericProjectionFinite.equation, map_sub, map_mul, map_C,
      ProjectionFiniteSpecialization.map_liftPolynomial_of_comp φ hφ, lift_pderiv_levelPolynomial]

end ChangeCoefficients

theorem eval_parameterDirection {L : Type*} [Field L] [Algebra K L]
    (base : ι) (a : L) (u : DirectionIndex base → L) (i : ι) :
    eval₂ (algebraMap K L) (fun t => t.elim a u) (parameterDirection (K := K) base i) =
      normalizedDirection base u i := by
  classical
  by_cases hi : i = base <;> simp [parameterDirection, normalizedDirection, hi]

theorem eval_equation {L : Type*} [Field L] [Algebra K L] (p : MvPolynomial ι K)
    (base : ι) (a : L) (u : DirectionIndex base → L) (z : Option ι → L) (j : Sum Bool ι) :
    (equation p base j).eval₂ (eval₂Hom (algebraMap K L) (fun t => t.elim a u)) z =
      aeval z (GenericProjectionFinite.equation (levelPolynomial p a) base (normalizedDirection base u) j) := by
  let φ := eval₂Hom (algebraMap K L) (fun t : Option (DirectionIndex base) => t.elim a u)
  have hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K L := by
    ext k
    simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, φ, eval₂Hom_C]
  have hd : (fun i => φ (parameterDirection (K := K) base i)) = normalizedDirection base u := by
    funext i
    exact eval_parameterDirection base a u i
  have he := map_equation p base φ hφ j
  have ha : φ (X none) = a := by simp [φ]
  rw [hd, ha] at he
  rw [← he, aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]

theorem exists_direction_derivations [CharZero K] [DecidableEq ι] (base : ι) :
    ∃ D : DirectionIndex base → Derivation K (ParameterField K base) (ParameterField K base),
      (∀ j, D j (genericLevel base) = 0) ∧
      ∀ j i, D j (genericDirection base i) = if i = j.val then 1 else 0 := by
  classical
  let A := ParameterRing K base
  let F := ParameterField K base
  let w : Option (DirectionIndex base) → F := fun t => algebraMap A F (X t)
  have hinj : Function.Injective (IsScalarTower.toAlgHom K A F) := IsFractionRing.injective A F
  have hind : AlgebraicIndependent K w := by
    have h := (MvPolynomial.algebraicIndependent_X (Option (DirectionIndex base)) K).map hinj.injOn
    change AlgebraicIndependent K (fun t => algebraMap A F (X t)) at h
    exact h
  have hex (j : DirectionIndex base) := CoordinateDerivation.exists_of_independent hind (some j)
  choose D hD using hex
  refine ⟨D, ?_, ?_⟩
  · intro j
    simpa [genericLevel, w] using hD j none
  · intro j i
    by_cases hi : i = base
    · subst i
      have hj : base ≠ j.val := Ne.symm j.property
      simp [genericDirection, parameterDirection_base, hj]
    · have h := hD j (some ⟨i, hi⟩)
      simpa [w, genericDirection, parameterDirection, hi, Subtype.ext_iff] using h

variable [Fintype ι]

theorem algebraic_generic_coordinates [CharZero K] {L : Type*} [Field L]
    [Algebra K L] (p : MvPolynomial ι K) (base : ι) [Algebra (ParameterField K base) L]
    [IsScalarTower K (ParameterField K base) L] (z : Option ι → L)
    (hz : ∀ j, aeval z (GenericProjectionFinite.equation (levelPolynomial p (genericLevel (K := K) base))
      base (genericDirection (K := K) base) j) = 0) : ∀ i, IsAlgebraic (ParameterField K base) (z i) := by
  classical
  let : CharZero (ParameterField K base) :=
    charZero_of_injective_algebraMap (algebraMap K (ParameterField K base)).injective
  obtain ⟨D, hlevel, hcoord⟩ := exists_direction_derivations (K := K) base
  apply ProjectionParameterCoordinates.algebraic_extended_coordinates
    (levelPolynomial p (genericLevel base)) base (genericDirection base) z
    (by rw [genericDirection, parameterDirection_base, map_one]) D
    (fun j => fixed_levelPolynomial (D j) p _ (hlevel j)) hcoord hz

universe uL

theorem exists_finite_specialization_polynomial [CharZero K] (p : MvPolynomial ι K) (base : ι) :
    ∃ d : ParameterRing K base, d ≠ 0 ∧ ∀ (L : Type uL) [Field L] (φ : ParameterRing K base →+* L),
      φ d ≠ 0 → {z : Option ι → L | ∀ j, (equation p base j).eval₂ φ z = 0}.Finite := by
  let A := ParameterRing K base
  let F := ParameterField K base
  let I : Ideal (MvPolynomial (Option ι) A) := Ideal.span (Set.range (equation p base))
  have hcoords : ∀ P ∈ (I.map (algebraMap (MvPolynomial (Option ι) A) (MvPolynomial (Option ι) F))).minimalPrimes,
      ∀ i, IsAlgebraic F (FiniteAlgebraicZeros.quotientPoint P i) := by
    intro P hP
    let : P.IsPrime := hP.isPrime
    let z := FiniteAlgebraicZeros.quotientPoint P
    have hz : ∀ j, aeval z (GenericProjectionFinite.equation (levelPolynomial p (genericLevel (K := K) base))
        base (genericDirection (K := K) base) j) = 0 := by
      intro j
      have he : algebraMap (MvPolynomial (Option ι) A) (MvPolynomial (Option ι) F) (equation p base j) =
          GenericProjectionFinite.equation (levelPolynomial p (genericLevel (K := K) base))
            base (genericDirection (K := K) base) j := by
        rw [MvPolynomial.algebraMap_def, map_equation p base (algebraMap A F)
          (IsScalarTower.algebraMap_eq K A F)]
        rfl
      rw [FiniteAlgebraicZeros.eval_quotientPoint]
      have hmem : GenericProjectionFinite.equation (levelPolynomial p (genericLevel (K := K) base))
          base (genericDirection (K := K) base) j ∈ P := by
        rw [← he]
        exact hP.le (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self j)))
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    exact algebraic_generic_coordinates p base z hz
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

theorem exists_exceptional_polynomial [CharZero K] (p : MvPolynomial ι K) (base : ι) :
    ∃ d : ParameterRing K base, d ≠ 0 ∧ ∀ (L : Type uL) [Field L] [Algebra K L]
      (a : L) (u : DirectionIndex base → L), eval₂ (algebraMap K L) (fun t => t.elim a u) d ≠ 0 →
        {z : Option ι → L | ∀ j, aeval z
          (GenericProjectionFinite.equation (levelPolynomial p a) base (normalizedDirection base u) j) = 0}.Finite := by
  obtain ⟨d, hd, hfinite⟩ := exists_finite_specialization_polynomial p base
  refine ⟨d, hd, ?_⟩
  intro L _ _ a u hu
  apply (hfinite L (eval₂Hom (algebraMap K L) (fun t => t.elim a u)) hu).subset
  intro z hz j
  rw [eval_equation]
  exact hz j

end LeanCanny.Algebra.LevelProjectionSpecialization
