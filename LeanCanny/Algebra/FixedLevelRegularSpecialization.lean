/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedLevelProjectionJacobian
public import LeanCanny.Algebra.RegularFiberSpecialization
public import LeanCanny.Algebra.CoordinateAnnihilatorSpecialization

/-! # Regular critical projections with a fixed hypersurface equation

The level need not be an independent parameter. Generic direction
derivations and denominator clearing produce an actual exceptional direction
polynomial for the fixed equation. A bounded integer direction leaves all
extended critical roots finite and nonsingular over every extension field.
The bound is qualitative in the exceptional polynomial, not in input size.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedLevelRegularSpecialization
open MvPolynomial ProjectionFiniteSpecialization
open scoped Classical
attribute [local instance] MvPolynomial.algebraMvPolynomial
set_option backward.isDefEq.respectTransparency false

universe u
variable {K ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def row (base : ι) : Option ι → Sum Bool ι
  | none => .inl true
  | some i => if i = base then .inl false else .inr i

noncomputable def square (q : MvPolynomial ι K) (base : ι) :
    Option ι → MvPolynomial (Option ι) (ParameterRing K base) :=
  fun i => GenericProjectionFinite.equation q base (parameterDirection base) (row base i)

noncomputable def jacobian (q : MvPolynomial ι K) (base : ι) :
    MvPolynomial (Option ι) (ParameterRing K base) :=
  Matrix.det (Matrix.of fun i j => pderiv j (square q base i))

omit [Fintype ι] in
theorem map_square {B : Type*} [Field B] [Algebra K B]
    (q : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B) (i : Option ι) :
    (square q base i).map φ = GenericProjectionJacobian.equation q base 0
      (fun j => φ (parameterDirection base j)) i := by
  rw [square, map_equation_of_comp φ hφ]
  cases i with
  | none => rfl
  | some i =>
    by_cases hi : i = base
    · simp only [row, hi, ite_true, GenericProjectionFinite.equation,
        GenericProjectionJacobian.equation, map_zero, sub_zero]
    · simp only [row, hi, ite_false, GenericProjectionFinite.equation,
        GenericProjectionJacobian.equation]

theorem map_jacobian {B : Type*} [Field B] [Algebra K B]
    (q : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B) :
    (jacobian q base).map φ = Matrix.det (fun i j => pderiv j
      (GenericProjectionJacobian.equation q base 0 (fun k => φ (parameterDirection base k)) i)) := by
  change (MvPolynomial.map φ) (Matrix.det (Matrix.of fun i j => pderiv j (square q base i))) = _
  rw [(MvPolynomial.map φ).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (square q base i)).map φ = _
  rw [← pderiv_map, map_square q base φ hφ]

theorem eval_jacobian {B : Type*} [Field B] [Algebra K B]
    (q : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B) (z : Option ι → B) :
    (jacobian q base).eval₂ φ z =
      (GenericProjectionJacobian.extended q base (fun k => φ (parameterDirection base k))
        (fun i => z (some i)) (z none)).det := by
  have hz : (fun k : Option ι => k.elim (z none) (fun i => z (some i))) = z := by
    funext k
    cases k <;> rfl
  have he := GenericProjectionJacobian.formalJacobian_eq q base 0
    (fun k => φ (parameterDirection base k)) (fun i => z (some i)) (z none)
  rw [hz] at he
  rw [← MvPolynomial.eval_map, map_jacobian q base φ hφ]
  change (MvPolynomial.eval z) (Matrix.det (Matrix.of fun i j => pderiv j
    (GenericProjectionJacobian.equation q base 0 (fun k => φ (parameterDirection base k)) i))) = _
  rw [(MvPolynomial.eval z).map_det]
  convert congrArg Matrix.det he using 1; rfl

theorem exists_exceptional [CharZero K] (q : MvPolynomial ι K) (base : ι) :
    ∃ d : ParameterRing K base, d ≠ 0 ∧
      ∀ (L : Type u) [Field L] (φ : ParameterRing K base →+* L) (z : Option ι → L),
        φ d ≠ 0 → (∀ j, (GenericProjectionFinite.equation q base (parameterDirection base) j).eval₂ φ z = 0) →
          (jacobian q base).eval₂ φ z ≠ 0 := by
  let A := ParameterRing K base
  let F := DirectionField K base
  apply RegularFiberSpecialization.exists_exceptional (F := F)
  intro L _ _ z hz
  let : Algebra K L := Algebra.compHom L (algebraMap K F)
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  have hmap (j : Sum Bool ι) :
      (GenericProjectionFinite.equation q base (parameterDirection base) j).map (algebraMap A F) =
        GenericProjectionFinite.equation q base (genericDirection (K := K) base) j := by
    rw [ProjectionFiniteSpecialization.map_equation]
    rfl
  have hroots : ∀ j, aeval z (GenericProjectionFinite.equation q base (genericDirection (K := K) base) j) = 0 := by
    intro j
    rw [← hmap]
    exact hz j
  obtain ⟨hq, hinv, hcritical⟩ :=
    (GenericProjectionFinite.equations_iff q base (genericDirection (K := K) base) z).mp hroots
  let v := fun i => algebraMap F L (genericDirection (K := K) base i)
  have hind : AlgebraicIndependent K (fun i : DirectionIndex base => v i) := by
    have hi : Function.Injective (IsScalarTower.toAlgHom K F L) := (algebraMap F L).injective
    have h := (independent_genericDirection (K := K) base).map hi.injOn
    convert h using 1
    rfl
  have hdet := FixedLevelProjectionJacobian.extended_det_ne_zero q base v
    (fun i => z (some i)) (z none) hind hq hcritical hinv
  let ψ : A →+* L := (algebraMap F L).comp (algebraMap A F)
  have hψ : ψ.comp (algebraMap K A) = algebraMap K L := by
    dsimp only [ψ]
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K A F, ← IsScalarTower.algebraMap_eq K F L]
  rw [aeval_def, eval₂_map]
  change (jacobian q base).eval₂ ψ z ≠ 0
  rw [eval_jacobian q base ψ hψ z]
  exact hdet

omit [DecidableEq ι] in
theorem nonempty_coordinate_certificate [CharZero K] (q : MvPolynomial ι K) (base : ι) :
    Nonempty (CoordinateAnnihilatorSpecialization.Certificate
      (GenericProjectionFinite.ideal q base (parameterDirection (K := K) base))) :=
  CoordinateAnnihilatorSpecialization.nonempty_certificate (F := DirectionField K base) _
    (generic_quotient_coordinates_algebraic q base)

/-- The same integer direction retains coordinate equations as well as finite
simple roots. The coefficient field may contain a separate sweep parameter. -/
theorem exists_nat_regular_coordinates [CharZero K] (q : MvPolynomial ι K) (base : ι) :
    ∃ B : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ B) ∧
      ∃ Q : Option ι → Polynomial K, (∀ i, Q i ≠ 0) ∧
      ∀ (L : Type u) [Field L] [Algebra K L],
        {z : Option ι → L | ∀ j, aeval z (GenericProjectionFinite.equation q base
          (normalizedDirection base (fun i => (u i : L))) j) = 0}.Finite ∧
        (∀ z : Option ι → L,
          (∀ j, aeval z (GenericProjectionFinite.equation q base
            (normalizedDirection base (fun i => (u i : L))) j) = 0) →
          (GenericProjectionJacobian.extended q base (normalizedDirection base (fun i => (u i : L)))
            (fun i => z (some i)) (z none)).det ≠ 0) ∧
        ∀ z : Option ι → L,
          (∀ j, aeval z (GenericProjectionFinite.equation q base
            (normalizedDirection base (fun i => (u i : L))) j) = 0) →
          ∀ i, Polynomial.aeval (z i) (Q i) = 0 := by
  obtain ⟨cert⟩ := nonempty_coordinate_certificate q base
  let df := cert.exceptional
  have hdf : df ≠ 0 := cert.exceptional_ne_zero
  obtain ⟨dr, hdr, hregular⟩ := exists_exceptional q base
  let d := df * dr
  obtain ⟨u, hu, hnonzero⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero d
    (mul_ne_zero hdf hdr) d.totalDegree le_rfl
  let φK : ParameterRing K base →+* K := MvPolynomial.eval (fun i => (u i : K))
  have hφKdf : φK df ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [d, map_mul] using hnonzero)).1
  let Q := fun i => (cert.polynomial i).map φK
  refine ⟨d.totalDegree, u, hu, Q, (fun i => cert.specialized_polynomial_ne_zero φK hφKdf i), ?_⟩
  intro L _ _
  let φ : ParameterRing K base →+* L := eval₂Hom (algebraMap K L) (fun i => (u i : L))
  have hφd : φ d ≠ 0 := by
    have he := MvPolynomial.hom_eval₂ d (RingHom.id K) (algebraMap K L) (fun i => (u i : K))
    simp only [eval₂_id, RingHom.comp_id, map_natCast] at he
    change d.eval₂ (algebraMap K L) (fun i => (u i : L)) ≠ 0
    rw [← he]
    exact fun h => hnonzero ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have hfac : φ df ≠ 0 ∧ φ dr ≠ 0 := mul_ne_zero_iff.mp (by simpa only [d, map_mul] using hφd)
  have hroots (z : Option ι → L)
      (hz : ∀ j, aeval z (GenericProjectionFinite.equation q base
        (normalizedDirection base (fun i => (u i : L))) j) = 0) :
      ∀ j, (GenericProjectionFinite.equation q base (parameterDirection base) j).eval₂ φ z = 0 := by
    intro j
    rw [eval_equation]
    exact hz j
  have hcomp : (algebraMap K L).comp φK = φ := by
    ext k <;> simp [φK, φ]
  have hI (z : Option ι → L)
      (hz : ∀ j, aeval z (GenericProjectionFinite.equation q base
        (normalizedDirection base (fun i => (u i : L))) j) = 0) :
      ∀ f ∈ GenericProjectionFinite.ideal q base (parameterDirection (K := K) base), f.eval₂ φ z = 0 := by
    have hk : GenericProjectionFinite.ideal q base (parameterDirection (K := K) base) ≤
        RingHom.ker (eval₂Hom φ z) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hroots z hz j
    exact fun _ hf => hk hf
  have hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K L := by
    ext k
    simp [φ]
  have hdir : (fun k => φ (parameterDirection base k)) = normalizedDirection base (fun i => (u i : L)) := by
    funext i
    exact eval_parameterDirection base (fun i => (u i : L)) i
  refine ⟨?_, ?_, ?_⟩
  · apply (cert.finite_solutions (E := L) φK hφKdf).subset
    intro z hz f hf
    rw [hcomp]
    exact hI z hz f hf
  · intro z hz
    have he := hregular L φ z hfac.2 (hroots z hz)
    rw [eval_jacobian q base φ hφ z, hdir] at he
    exact he
  · intro z hz i
    apply cert.aeval_specialized_eq_zero φK hφKdf z
    intro f hf
    rw [hcomp]
    exact hI z hz f hf

/-- Regularity and finiteness without exposing the retained coordinate equations. -/
theorem exists_nat_regular_fiber [CharZero K] (q : MvPolynomial ι K) (base : ι) :
    ∃ B : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ B) ∧
      ∀ (L : Type u) [Field L] [Algebra K L],
        {z : Option ι → L | ∀ j, aeval z (GenericProjectionFinite.equation q base
          (normalizedDirection base (fun i => (u i : L))) j) = 0}.Finite ∧
        ∀ z : Option ι → L,
          (∀ j, aeval z (GenericProjectionFinite.equation q base
            (normalizedDirection base (fun i => (u i : L))) j) = 0) →
          (GenericProjectionJacobian.extended q base (normalizedDirection base (fun i => (u i : L)))
            (fun i => z (some i)) (z none)).det ≠ 0 := by
  obtain ⟨B, u, hu, _, _, h⟩ := exists_nat_regular_coordinates q base
  exact ⟨B, u, hu, fun L _ _ => ⟨(h L).1, (h L).2.1⟩⟩

end LeanCanny.Algebra.FixedLevelRegularSpecialization
