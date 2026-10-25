/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedLevelRegularSpecialization

/-! # Native critical equations over a parameter ring

The coefficients need not form a field. In particular, a polynomial slice
can keep its sweep parameter in the coefficient ring. Mapping coefficients
commutes with the actual critical equations and their formal Jacobian, so
generic field certificates can be cleared and specialized in this system.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionCriticalFamily
open MvPolynomial
open scoped Classical

variable {A ι : Type*} [CommRing A] [DecidableEq ι]

noncomputable def equation (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    Sum Bool ι → MvPolynomial (Option ι) A
  | .inl false => rename some q
  | .inl true => X none * rename some (pderiv base q) - 1
  | .inr i => rename some (pderiv i q) - C (v i) * rename some (pderiv base q)

noncomputable def ideal (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    Ideal (MvPolynomial (Option ι) A) := Ideal.span (Set.range (equation q base v))

noncomputable def square (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    Option ι → MvPolynomial (Option ι) A :=
  fun i => equation q base v (FixedLevelRegularSpecialization.row base i)

noncomputable def jacobian [Fintype ι] (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    MvPolynomial (Option ι) A := Matrix.det (Matrix.of fun i j => pderiv j (square q base v i))

/-- The spatial system omits the reciprocal, which need not stay bounded at
critical endpoints even when the original points do. -/
noncomputable def spatialEquation (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    ι → MvPolynomial ι A := fun i =>
  if i = base then q else pderiv i q - C (v i) * pderiv base q

noncomputable def spatialJacobian [Fintype ι] (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    MvPolynomial ι A := Matrix.det (Matrix.of fun i j => pderiv j (spatialEquation q base v i))

theorem spatial_zero_iff {B : Type*} [CommRing B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) (hv : φ (v base) = 1) (x : ι → B) :
    (∀ i, (spatialEquation q base v i).eval₂ φ x = 0) ↔
      q.eval₂ φ x = 0 ∧ ∀ i, (pderiv i q).eval₂ φ x = φ (v i) * (pderiv base q).eval₂ φ x := by
  constructor
  · intro h
    refine ⟨by simpa only [spatialEquation, ite_true] using h base, ?_⟩
    intro i
    by_cases hi : i = base
    · simp only [hi, hv, one_mul]
    · simpa only [spatialEquation, ite_eq_right hi, eval₂_sub, eval₂_mul, eval₂_C, sub_eq_zero] using h i
  · rintro ⟨hq, hpartial⟩ i
    by_cases hi : i = base
    · simpa only [spatialEquation, ite_eq_left hi] using hq
    · simp only [spatialEquation, ite_eq_right hi, eval₂_sub, eval₂_mul, eval₂_C,
        hpartial i, sub_self]

theorem eval_spatialJacobian [Fintype ι] {B : Type*} [Field B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) (x : ι → B) :
    (spatialJacobian q base v).eval₂ φ x =
      (GenericProjectionJacobian.spatial (q.map φ) base (fun i => φ (v i)) x).det := by
  change (eval₂Hom φ x) (Matrix.det (Matrix.of fun i j => pderiv j (spatialEquation q base v i))) = _
  rw [(eval₂Hom φ x).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (spatialEquation q base v i)).eval₂ φ x = _
  by_cases hi : i = base
  · simp only [spatialEquation, hi, ite_true, GenericProjectionJacobian.spatial, pderiv_map,
      aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]
  · simp only [spatialEquation, ite_eq_right hi, map_sub, pderiv_mul, pderiv_C, zero_mul,
      zero_add, eval₂_sub, eval₂_mul, eval₂_C, GenericProjectionJacobian.spatial, pderiv_map,
      aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]

omit [DecidableEq ι] in
theorem equations_iff {B : Type*} [CommRing B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) (z : Option ι → B) :
    (∀ j, (equation q base v j).eval₂ φ z = 0) ↔
      let x := fun i => z (some i)
      q.eval₂ φ x = 0 ∧ z none * (pderiv base q).eval₂ φ x = 1 ∧
        ∀ i, (pderiv i q).eval₂ φ x = φ (v i) * (pderiv base q).eval₂ φ x := by
  simp only [Sum.forall, Bool.forall_bool, equation, eval₂_sub, eval₂_mul,
    eval₂_rename, eval₂_X, eval₂_one, eval₂_C, Function.comp_def, sub_eq_zero, and_assoc]

omit [DecidableEq ι] in
theorem map_equation {B : Type*} [Field B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) (j : Sum Bool ι) :
    (equation q base v j).map φ =
      GenericProjectionFinite.equation (q.map φ) base (fun i => φ (v i)) j := by
  rcases j with b | i
  · cases b <;> simp only [equation, GenericProjectionFinite.equation,
      GenericProjectionFinite.liftPolynomial, map_sub, map_mul, map_one, map_X,
      map_rename, Algebra.algebraMap_self, MvPolynomial.map_id, pderiv_map]
  · simp only [equation, GenericProjectionFinite.equation, GenericProjectionFinite.liftPolynomial,
      map_sub, map_mul, map_C, map_rename, Algebra.algebraMap_self, MvPolynomial.map_id, pderiv_map]

theorem map_square {B : Type*} [Field B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) (i : Option ι) :
    (square q base v i).map φ =
      GenericProjectionJacobian.equation (q.map φ) base 0 (fun j => φ (v j)) i := by
  rw [square, map_equation]
  cases i with
  | none => rfl
  | some i =>
    by_cases hi : i = base
    · simp only [FixedLevelRegularSpecialization.row, hi, ite_true, GenericProjectionFinite.equation,
        GenericProjectionJacobian.equation, map_zero, sub_zero]
    · simp only [FixedLevelRegularSpecialization.row, hi, ite_false, GenericProjectionFinite.equation,
        GenericProjectionJacobian.equation]

theorem map_jacobian [Fintype ι] {B : Type*} [Field B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) :
    (jacobian q base v).map φ = Matrix.det (fun i j => pderiv j
      (GenericProjectionJacobian.equation (q.map φ) base 0 (fun k => φ (v k)) i)) := by
  change (MvPolynomial.map φ) (Matrix.det (Matrix.of fun i j => pderiv j (square q base v i))) = _
  rw [(MvPolynomial.map φ).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (square q base v i)).map φ = _
  rw [← pderiv_map, map_square]

theorem eval_jacobian [Fintype ι] {B : Type*} [Field B] (φ : A →+* B)
    (q : MvPolynomial ι A) (base : ι) (v : ι → A) (z : Option ι → B) :
    (jacobian q base v).eval₂ φ z =
      (GenericProjectionJacobian.extended (q.map φ) base (fun k => φ (v k))
        (fun i => z (some i)) (z none)).det := by
  have hz : (fun k : Option ι => k.elim (z none) (fun i => z (some i))) = z := by
    funext k
    cases k <;> rfl
  have he := GenericProjectionJacobian.formalJacobian_eq (q.map φ) base 0
    (fun k => φ (v k)) (fun i => z (some i)) (z none)
  rw [hz] at he
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at he
  rw [← MvPolynomial.eval_map, map_jacobian]
  change (MvPolynomial.eval z) (Matrix.det (Matrix.of fun i j => pderiv j
    (GenericProjectionJacobian.equation (q.map φ) base 0 (fun k => φ (v k)) i))) = _
  rw [(MvPolynomial.eval z).map_det]
  convert congrArg Matrix.det he using 1; rfl

theorem map_nat_direction {B : Type*} [CommRing B] (φ : A →+* B) (base : ι)
    (u : ProjectionFiniteSpecialization.DirectionIndex base → ℕ) :
    (fun i => φ (ProjectionFiniteSpecialization.normalizedDirection base (fun j => (u j : A)) i)) =
      ProjectionFiniteSpecialization.normalizedDirection base (fun j => (u j : B)) := by
  funext i
  by_cases hi : i = base <;>
    simp only [ProjectionFiniteSpecialization.normalizedDirection, hi, dite_true, dite_false,
      map_one, map_natCast]

omit [DecidableEq ι] in
theorem equations_map_iff {F L : Type*} [Field F] [Field L] [Algebra F L]
    (φ : A →+* F) (q : MvPolynomial ι A) (base : ι) (v : ι → A) (z : Option ι → L) :
    (∀ j, aeval z ((equation q base v j).map φ) = 0) ↔
      ∀ j, aeval z (GenericProjectionFinite.equation (q.map φ) base
        (fun i => algebraMap F L (φ (v i))) j) = 0 := by
  have hφ : (algebraMap F L).comp (algebraMap F F) = algebraMap F L := by
    simp only [Algebra.algebraMap_self, RingHom.comp_id]
  have he (j : Sum Bool ι) := ProjectionFiniteSpecialization.map_equation_of_comp
    (algebraMap F L) hφ (q.map φ) base (fun i => φ (v i)) j
  have hpoint (j : Sum Bool ι) : aeval z ((equation q base v j).map φ) =
      aeval z (GenericProjectionFinite.equation (q.map φ) base (fun i => algebraMap F L (φ (v i))) j) := by
    rw [map_equation, ← he j]
    simp only [aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]
  simp only [hpoint]

private theorem extended_map [Fintype ι] {F L : Type*} [Field F] [Field L] [Algebra F L]
    (q : MvPolynomial ι F) (base : ι) (v x : ι → L) (u : L) :
    GenericProjectionJacobian.extended (q.map (algebraMap F L)) base v x u =
      GenericProjectionJacobian.extended q base v x u := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp only [GenericProjectionJacobian.extended, GenericProjectionJacobian.spatial,
      pderiv_map, aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]

theorem aeval_mapped_jacobian [Fintype ι] {F L : Type*} [Field F] [Field L] [Algebra F L]
    (φ : A →+* F) (q : MvPolynomial ι A) (base : ι) (v : ι → A) (z : Option ι → L) :
    aeval z ((jacobian q base v).map φ) =
      (GenericProjectionJacobian.extended (q.map φ) base (fun i => algebraMap F L (φ (v i)))
        (fun i => z (some i)) (z none)).det := by
  rw [aeval_def, eval₂_map, eval_jacobian, ← MvPolynomial.map_map, extended_map]
  rfl

end LeanCanny.Algebra.ProjectionCriticalFamily
