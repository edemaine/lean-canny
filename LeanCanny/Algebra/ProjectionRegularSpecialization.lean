/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericProjectionJacobian
public import LeanCanny.Algebra.RegularFiberSpecialization
public import LeanCanny.Algebra.ParameterLineSpecialization

/-! # Exceptional polynomials for nonsingular projection-critical roots

The symbolic level and normalized direction equations have an actual square
Jacobian. Generic nonsingularity and denominator clearing give a nonzero joint
parameter polynomial outside which all specialized critical roots are simple.
The square equations include the reciprocal of the base partial derivative.
This result does not yet bound the exceptional polynomial's representation.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionRegularSpecialization
open MvPolynomial LevelProjectionSpecialization
attribute [local instance] MvPolynomial.algebraMvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

universe u
variable {K ι : Type u} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def row (base : ι) : Option ι → Sum Bool ι
  | none => .inl true
  | some i => if i = base then .inl false else .inr i

noncomputable def square (p : MvPolynomial ι K) (base : ι) :
    Option ι → MvPolynomial (Option ι) (ParameterRing K base) :=
  fun i => LevelProjectionSpecialization.equation p base (row base i)

noncomputable def jacobian (p : MvPolynomial ι K) (base : ι) :
    MvPolynomial (Option ι) (ParameterRing K base) :=
  Matrix.det (Matrix.of fun i j => pderiv j (square p base i))

omit [Fintype ι] in
theorem map_square {B : Type*} [Field B] [Algebra K B]
    (p : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B) (i : Option ι) :
    (square p base i).map φ = GenericProjectionJacobian.equation p base
      (φ (X none)) (fun j => φ (parameterDirection base j)) i := by
  rw [square, LevelProjectionSpecialization.map_equation p base φ hφ]
  cases i with
  | none =>
    simp only [row, GenericProjectionFinite.equation, GenericProjectionJacobian.equation,
      lift_pderiv_levelPolynomial]
  | some i =>
    by_cases hi : i = base
    · simp only [row, hi, ite_true, GenericProjectionFinite.equation,
        GenericProjectionJacobian.equation, lift_levelPolynomial]
    · simp only [row, hi, ite_false, GenericProjectionFinite.equation,
        GenericProjectionJacobian.equation, lift_pderiv_levelPolynomial]

theorem map_jacobian {B : Type*} [Field B] [Algebra K B]
    (p : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B) :
    (jacobian p base).map φ = Matrix.det (fun i j => pderiv j
      (GenericProjectionJacobian.equation p base (φ (X none))
        (fun k => φ (parameterDirection base k)) i)) := by
  change (MvPolynomial.map φ)
    (Matrix.det (Matrix.of fun i j => pderiv j (square p base i))) = _
  rw [(MvPolynomial.map φ).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (square p base i)).map φ = _
  rw [← pderiv_map, map_square p base φ hφ]

/-- Specializing the native determinant gives precisely the extended
projection-critical Jacobian already proved nonsingular generically. -/
theorem eval_jacobian {B : Type*} [Field B] [Algebra K B]
    (p : MvPolynomial ι K) (base : ι) (φ : ParameterRing K base →+* B)
    (hφ : φ.comp (algebraMap K (ParameterRing K base)) = algebraMap K B)
    (z : Option ι → B) :
    (jacobian p base).eval₂ φ z =
      (GenericProjectionJacobian.extended p base (fun k => φ (parameterDirection base k))
        (fun i => z (some i)) (z none)).det := by
  have hz : (fun k : Option ι => k.elim (z none) (fun i => z (some i))) = z := by
    funext k
    cases k <;> rfl
  have he := GenericProjectionJacobian.formalJacobian_eq p base
    (φ (X none)) (fun k => φ (parameterDirection base k)) (fun i => z (some i)) (z none)
  rw [hz] at he
  rw [← MvPolynomial.eval_map, map_jacobian p base φ hφ]
  change (MvPolynomial.eval z) (Matrix.det (Matrix.of fun i j => pderiv j
    (GenericProjectionJacobian.equation p base (φ (X none))
      (fun k => φ (parameterDirection base k)) i))) = _
  rw [(MvPolynomial.eval z).map_det]
  convert congrArg Matrix.det he using 1; rfl

/-- The exceptional factor is constructed for the original critical equations
and their square Jacobian, not for an assumed smooth replacement system. -/
theorem exists_exceptional [CharZero K] (p : MvPolynomial ι K) (base : ι) :
    ∃ d : ParameterRing K base, d ≠ 0 ∧
      ∀ (L : Type u) [Field L] (φ : ParameterRing K base →+* L) (z : Option ι → L),
        φ d ≠ 0 → (∀ j, (LevelProjectionSpecialization.equation p base j).eval₂ φ z = 0) →
          (jacobian p base).eval₂ φ z ≠ 0 := by
  let A := ParameterRing K base
  let F := ParameterField K base
  apply RegularFiberSpecialization.exists_exceptional (F := F)
  intro L _ _ z hz
  let : Algebra K L := Algebra.compHom L (algebraMap K F)
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  have hmap (j : Sum Bool ι) :
      (LevelProjectionSpecialization.equation p base j).map (algebraMap A F) =
        GenericProjectionFinite.equation (levelPolynomial p (genericLevel (K := K) base))
          base (genericDirection (K := K) base) j := by
    rw [LevelProjectionSpecialization.map_equation p base (algebraMap A F)
      (IsScalarTower.algebraMap_eq K A F)]
    rfl
  have hroots : ∀ j, aeval z (GenericProjectionFinite.equation
      (levelPolynomial p (genericLevel (K := K) base)) base (genericDirection (K := K) base) j) = 0 := by
    intro j
    rw [← hmap]
    exact hz j
  have hdet := GenericProjectionJacobian.generic_formalJacobian_det_ne_zero p base z hroots
  let ψ : A →+* L := (algebraMap F L).comp (algebraMap A F)
  have hψ : ψ.comp (algebraMap K A) = algebraMap K L := by
    dsimp only [ψ]
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K A F,
      ← IsScalarTower.algebraMap_eq K F L]
  rw [aeval_def, eval₂_map]
  change (jacobian p base).eval₂ ψ z ≠ 0
  rw [← MvPolynomial.eval_map, map_jacobian p base ψ hψ]
  change (MvPolynomial.eval z) (Matrix.det (Matrix.of fun i j => pderiv j
    (GenericProjectionJacobian.equation p base (ψ (X none))
      (fun k => ψ (parameterDirection base k)) i))) ≠ 0
  rw [(MvPolynomial.eval z).map_det]
  change (Matrix.det (Matrix.of fun i j => (MvPolynomial.eval z) (pderiv j
    (GenericProjectionJacobian.equation p base (ψ (X none))
      (fun k => ψ (parameterDirection base k)) i)))) ≠ 0
  convert hdet using 1; rfl

/-- One integer direction has finite, nonsingular critical fibers away from
the roots of one nonzero univariate level polynomial. The size bound `B`
comes from the constructed joint exceptional polynomial; no polynomial
input-size estimate for `B` is asserted. -/
theorem exists_nat_regular_levels [CharZero K] (p : MvPolynomial ι K) (base : ι) :
    ∃ B : ℕ, ∃ u : ProjectionFiniteSpecialization.DirectionIndex base → ℕ,
      (∀ i, u i ≤ B) ∧ ∃ r : Polynomial K, r ≠ 0 ∧ r.natDegree ≤ B ∧
        ∀ (L : Type u) [Field L] [Algebra K L] (a : L), Polynomial.aeval a r ≠ 0 →
          {z : Option ι → L | ∀ j, aeval z (GenericProjectionFinite.equation
            (levelPolynomial p a) base
              (ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : L))) j) = 0}.Finite ∧
          ∀ z : Option ι → L,
            (∀ j, aeval z (GenericProjectionFinite.equation (levelPolynomial p a) base
              (ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : L))) j) = 0) →
            (jacobian p base).eval₂
              (eval₂Hom (algebraMap K L) (fun i => i.elim a (fun j => (u j : L)))) z ≠ 0 := by
  classical
  obtain ⟨df, hdf, hfinite⟩ := LevelProjectionSpecialization.exists_finite_specialization_polynomial p base
  obtain ⟨dr, hdr, hregular⟩ := exists_exceptional p base
  let d := df * dr
  obtain ⟨u, hu, hr, hdegree⟩ := ParameterLineSpecialization.exists_nat_line_nonzero d (mul_ne_zero hdf hdr)
  let r := ParameterLineSpecialization.lineHom (fun i => (u i : K)) d
  refine ⟨d.totalDegree, u, hu, r, hr, hdegree, ?_⟩
  intro L _ _ a ha
  let φ : ParameterRing K base →+* L :=
    eval₂Hom (algebraMap K L) (fun i => i.elim a (fun j => (u j : L)))
  have hφd : φ d ≠ 0 := by
    have he := ParameterLineSpecialization.aeval_line (L := L) (fun i => (u i : K)) d a
    change Polynomial.aeval a (ParameterLineSpecialization.lineHom (fun i => (u i : K)) d) ≠ 0 at ha
    rw [he] at ha
    change eval₂ (algebraMap K L) (fun i => i.elim a (fun j => (u j : L))) d ≠ 0
    simpa only [map_natCast] using ha
  have hφdf : φ df ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [d, map_mul] using hφd)).1
  have hφdr : φ dr ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [d, map_mul] using hφd)).2
  have hroots (z : Option ι → L)
      (hz : ∀ j, aeval z (GenericProjectionFinite.equation (levelPolynomial p a) base
        (ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : L))) j) = 0) :
      ∀ j, (LevelProjectionSpecialization.equation p base j).eval₂ φ z = 0 := by
    intro j
    rw [LevelProjectionSpecialization.eval_equation]
    exact hz j
  refine ⟨(hfinite L φ hφdf).subset (fun z hz => hroots z hz), ?_⟩
  intro z hz
  exact hregular L φ z hφdr (hroots z hz)

end LeanCanny.Algebra.ProjectionRegularSpecialization
