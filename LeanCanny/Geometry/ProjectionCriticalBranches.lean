/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialRootFamily
public import LeanCanny.Algebra.ProjectionRegularSpecialization
public import LeanCanny.Algebra.CriticalValueAnnihilator

/-! # Regular branches of spatial projection-critical equations

The actual equations retain the hypersurface level as a polynomial parameter.
They omit the auxiliary reciprocal variable, which may diverge at a critical
endpoint even when the spatial curve is bounded. Their root projection is
proper whenever the level function is proper. A suitable integer direction
and a nonzero exceptional level polynomial give regular fibers.

This constructs regular critical-curve systems. It does not yet establish
that their union with recursive slices preserves all components of an
arbitrary semialgebraic input, or bound their effective representation sizes.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCriticalBranches
open MvPolynomial Set
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def equation (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ) :
    ι → MvPolynomial ι (Polynomial ℝ) := fun i =>
  if i = base then p.map Polynomial.C - C Polynomial.X else
    (pderiv i p).map Polynomial.C - C (Polynomial.C (v i)) * (pderiv base p).map Polynomial.C

omit [Fintype ι] [DecidableEq ι] in
theorem eval_map_C (p : MvPolynomial ι ℝ) (t : ℝ) (x : ι → ℝ) :
    (p.map Polynomial.C).eval₂ (Polynomial.evalRingHom t) x = p.eval x := by
  rw [eval₂_map]
  have hcomp : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext a
    exact Polynomial.eval_C
  rw [hcomp, eval₂_id]

omit [Fintype ι] in
theorem value_iff (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ) (hv : v base = 1)
    (t : ℝ) (x : ι → ℝ) :
    PolynomialRootFamily.value (equation p base v) (t, x) = 0 ↔
      p.eval x = t ∧ ∀ i, (pderiv i p).eval x = v i * (pderiv base p).eval x := by
  constructor
  · intro h
    have hrow (i : ι) := congrFun h i
    have hbase := hrow base
    simp only [PolynomialRootFamily.value, equation, ite_true, eval₂_sub, eval₂_C,
      eval_map_C, Polynomial.coe_evalRingHom, Polynomial.eval_X, Pi.zero_apply, sub_eq_zero] at hbase
    refine ⟨hbase, ?_⟩
    intro i
    by_cases hi : i = base
    · simp only [hi, hv, one_mul]
    · have h := hrow i
      simpa only [PolynomialRootFamily.value, equation, hi, ite_false, eval₂_sub, eval₂_mul,
        eval₂_C, eval_map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Pi.zero_apply, sub_eq_zero] using h
  · rintro ⟨hlevel, hpartial⟩
    funext i
    by_cases hi : i = base
    · simp only [PolynomialRootFamily.value, equation, hi, ite_true, eval₂_sub,
        eval_map_C, eval₂_C, Polynomial.coe_evalRingHom, Polynomial.eval_X, hlevel, sub_self, Pi.zero_apply]
    · simp only [PolynomialRootFamily.value, equation, hi, ite_false, eval₂_sub,
        eval₂_mul, eval₂_C, eval_map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        hpartial i, sub_self, Pi.zero_apply]

theorem eval_jacobian (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (t : ℝ) (x : ι → ℝ) :
    (PolynomialRootFamily.jacobian (equation p base v)).eval₂ (Polynomial.evalRingHom t) x =
      (GenericProjectionJacobian.spatial p base v x).det := by
  rw [PolynomialRootFamily.eval_jacobian (equation p base v) (t, x)]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  by_cases hi : i = base
  · simp only [equation, hi, ite_true, map_sub, pderiv_C, sub_zero, pderiv_map,
      eval_map_C, GenericProjectionJacobian.spatial, ite_true, aeval_def,
      Algebra.algebraMap_self, eval₂_id]
  · simp only [equation, hi, ite_false, map_sub, pderiv_mul, pderiv_C, zero_mul,
      zero_add, pderiv_map, eval₂_sub, eval₂_mul, eval₂_C, eval_map_C,
      Polynomial.coe_evalRingHom, Polynomial.eval_C, GenericProjectionJacobian.spatial,
      aeval_def, Algebra.algebraMap_self, eval₂_id]

/-- Properness belongs to the spatial critical curve even when the auxiliary
reciprocal is unbounded near exceptional endpoint levels. -/
theorem isProperMap (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ) (hv : v base = 1)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    IsProperMap (RootProjection.projection (PolynomialRootFamily.value (equation p base v))) :=
  PolynomialRootFamily.isProperMap_of_level _ hp
    (fun t x hx => ((value_iff p base v hv t x).mp hx).1.symm)

omit [Fintype ι] [DecidableEq ι] in
private theorem extended_root (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (t : ℝ) (x : ι → ℝ) (hlevel : p.eval x = t)
    (hpartial : ∀ i, (pderiv i p).eval x = v i * (pderiv base p).eval x)
    (hb : (pderiv base p).eval x ≠ 0) :
    ∀ j, aeval (fun k : Option ι => k.elim ((pderiv base p).eval x)⁻¹ x)
      (GenericProjectionFinite.equation (LevelProjectionSpecialization.levelPolynomial p t) base v j) = 0 := by
  apply (GenericProjectionFinite.equations_iff _ base v _).mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa [LevelProjectionSpecialization.levelPolynomial, aeval_def] using sub_eq_zero.mpr hlevel
  · simpa [LevelProjectionSpecialization.pderiv_levelPolynomial, aeval_def] using inv_mul_cancel₀ hb
  · intro i
    simpa [LevelProjectionSpecialization.pderiv_levelPolynomial, aeval_def] using hpartial i

/-- The integer direction and all exceptional levels are constructed from the
input polynomial. Outside that finite set, the spatial Jacobian is invertible;
no regularity hypothesis on the input hypersurface is required. -/
theorem exists_regular_direction (p : MvPolynomial ι ℝ) (base : ι) :
    ∃ u : ProjectionFiniteSpecialization.DirectionIndex base → ℕ,
      ∃ r : Polynomial ℝ, r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
        let v := ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
        ∀ t x, r.eval t ≠ 0 → PolynomialRootFamily.value (equation p base v) (t, x) = 0 →
          (PolynomialRootFamily.jacobian (equation p base v)).eval₂ (Polynomial.evalRingHom t) x ≠ 0 := by
  obtain ⟨_, u, _, r, hr, _, hregular⟩ := ProjectionRegularSpecialization.exists_nat_regular_levels p base
  obtain ⟨c, hc, hcm⟩ := CriticalValueAnnihilator.exists_annihilator p
  refine ⟨u, r * c, mul_ne_zero hr hc,
    Polynomial.finite_setOfPred_isRoot (mul_ne_zero hr hc), ?_⟩
  let v := ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
  have hv : v base = 1 := by simp [v, ProjectionFiniteSpecialization.normalizedDirection]
  dsimp only
  intro t x hnonzero hx
  have hfac : r.eval t ≠ 0 ∧ c.eval t ≠ 0 := mul_ne_zero_iff.mp (by
    simpa only [Polynomial.eval_mul] using hnonzero)
  obtain ⟨hlevel, hpartial⟩ := (value_iff p base v hv t x).mp hx
  have hb : (pderiv base p).eval x ≠ 0 := by
    intro hb
    have hgrad (i : ι) : aeval x (pderiv i p) = 0 := by
      simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, hpartial i, hb, mul_zero]
    have he := CriticalValueAnnihilator.eval_annihilator p c hcm x hgrad
    have hpval : aeval x p = t := by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hlevel
    rw [hpval] at he
    exact hfac.2 he
  let z : Option ι → ℝ := fun k => k.elim ((pderiv base p).eval x)⁻¹ x
  have hz := extended_root p base v t x hlevel hpartial hb
  have hrval : Polynomial.aeval t r ≠ 0 := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hfac.1
  have hdet := (hregular ℝ t hrval).2 z hz
  let φ : LevelProjectionSpecialization.ParameterRing ℝ base →+* ℝ :=
    eval₂Hom (RingHom.id ℝ) (fun i => i.elim t (fun j => (u j : ℝ)))
  have hφ : φ.comp (algebraMap ℝ (LevelProjectionSpecialization.ParameterRing ℝ base)) = algebraMap ℝ ℝ := by
    ext a
    simp [φ]
  have hdir : (fun i => φ (LevelProjectionSpecialization.parameterDirection base i)) = v := by
    funext i
    exact LevelProjectionSpecialization.eval_parameterDirection base t (fun j => (u j : ℝ)) i
  change (ProjectionRegularSpecialization.jacobian p base).eval₂ φ z ≠ 0 at hdet
  rw [ProjectionRegularSpecialization.eval_jacobian p base φ hφ z,
    hdir, GenericProjectionJacobian.extended_det] at hdet
  rw [eval_jacobian]
  exact (mul_ne_zero_iff.mp hdet).1

/-- Proper level functions yield actual finite-sheeted coverings between the
constructed exceptional levels. The original polynomial may be singular at
the excluded levels. -/
theorem exists_regular_covering (p : MvPolynomial ι ℝ) (base : ι)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ u : ProjectionFiniteSpecialization.DirectionIndex base → ℕ,
      ∃ r : Polynomial ℝ, r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
        let v := ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
        IsCoveringMapOn (RootProjection.projection (PolynomialRootFamily.value (equation p base v)))
          {t | r.eval t ≠ 0} := by
  obtain ⟨u, r, hr, hfinite, hregular⟩ := exists_regular_direction p base
  refine ⟨u, r, hr, hfinite, ?_⟩
  let v := ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
  have hv : v base = 1 := by simp [v, ProjectionFiniteSpecialization.normalizedDirection]
  apply RootProjection.isCoveringMapOn _ _ (isProperMap p base v hv hp)
  · intro z _
    exact (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  · intro z hz
    exact (PolynomialRootFamily.isInvertible_iff _ z.val).mpr
      (hregular z.val.1 z.val.2 hz z.property)

end LeanCanny.Geometry.ProjectionCriticalBranches
