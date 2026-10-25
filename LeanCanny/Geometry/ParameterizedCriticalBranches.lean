/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformCriticalSpecialization
public import LeanCanny.Geometry.PolynomialRootFamily
public import LeanCanny.Geometry.RootBranchCount
public import LeanCanny.Geometry.ComponentCriticalSampling

/-! # Regular spatial critical systems for polynomial parameter families

One integer direction and one finite exceptional parameter set are constructed
for the entire family. At regular slice roots, the reciprocal can be introduced
temporarily to transfer the generic Jacobian and coordinate certificates. It
is omitted from the spatial family, so its divergence cannot obstruct spatial
endpoint limits. Properness and slice regularity still belong to the caller.
-/

@[expose] public section

namespace LeanCanny.Geometry.ParameterizedCriticalBranches
open MvPolynomial Set
open LeanCanny.Algebra
open ProjectionFiniteSpecialization

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def system (q : MvPolynomial ι (Polynomial ℝ)) (base : ι)
    (u : DirectionIndex base → ℕ) : ℝ × (ι → ℝ) → ι → ℝ :=
  PolynomialRootFamily.value (ProjectionCriticalFamily.spatialEquation q base
    (normalizedDirection base (fun i => (u i : Polynomial ℝ))))

omit [Fintype ι] in
theorem system_iff (q : MvPolynomial ι (Polynomial ℝ)) (base : ι)
    (u : DirectionIndex base → ℕ) (t : ℝ) (x : ι → ℝ) :
    system q base u (t, x) = 0 ↔
      q.eval₂ (Polynomial.evalRingHom t) x = 0 ∧
        ∀ i, (pderiv i q).eval₂ (Polynomial.evalRingHom t) x =
          normalizedDirection base (fun i => (u i : ℝ)) i *
            (pderiv base q).eval₂ (Polynomial.evalRingHom t) x := by
  rw [funext_iff]
  change (∀ i, (ProjectionCriticalFamily.spatialEquation q base
    (normalizedDirection base (fun i => (u i : Polynomial ℝ))) i).eval₂
      (Polynomial.evalRingHom t) x = 0) ↔ _
  rw [ProjectionCriticalFamily.spatial_zero_iff]
  · simp only [congrFun (ProjectionCriticalFamily.map_nat_direction
      (Polynomial.evalRingHom t) base u)]
  · simp [normalizedDirection]

/-- Every component of a compact regular specialized level has a sample in
the same parameter-ring critical system used for continuation. -/
theorem exists_joined_critical (q : MvPolynomial ι (Polynomial ℝ)) (base : ι)
    (u : DirectionIndex base → ℕ) (t : ℝ)
    (hcompact : IsCompact {x : ι → ℝ | q.eval₂ (Polynomial.evalRingHom t) x = 0})
    (hregular : ∀ x : ι → ℝ, q.eval₂ (Polynomial.evalRingHom t) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => q.eval₂ (Polynomial.evalRingHom t) y) x))
    (x : ι → ℝ) (hx : q.eval₂ (Polynomial.evalRingHom t) x = 0) :
    ∃ y : ι → ℝ, JoinedIn {z | q.eval₂ (Polynomial.evalRingHom t) z = 0} x y ∧
      system q base u (t, y) = 0 := by
  let p := q.map (Polynomial.evalRingHom t)
  let v := normalizedDirection base (fun i => (u i : ℝ))
  have he (y : ι → ℝ) : p.eval y = q.eval₂ (Polynomial.evalRingHom t) y :=
    MvPolynomial.eval_map _ _ _
  have heq : (fun y => p.eval y) = (fun y => q.eval₂ (Polynomial.evalRingHom t) y) := funext he
  obtain ⟨y, hj, hy⟩ := ComponentCriticalSampling.exists_joined_critical p base v
    (by simp [v, normalizedDirection]) 0 (by simpa only [he] using hcompact)
    (fun y hy => by rw [heq]; exact hregular y ((he y).symm.trans hy)) x ((he x).trans hx)
  refine ⟨y, by simpa only [he] using hj, (system_iff q base u t y).mpr ?_⟩
  obtain ⟨hy0, hyp⟩ := (ProjectionCriticalBranches.value_iff p base v
    (by simp [v, normalizedDirection]) 0 y).mp hy
  refine ⟨(he y).symm.trans hy0, ?_⟩
  simpa only [p, pderiv_map, eval_map] using hyp

theorem exists_regular_system (q : MvPolynomial ι (Polynomial ℝ)) (base : ι) :
    ∃ u : DirectionIndex base → ℕ, ∃ r : Polynomial ℝ,
      r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
      ∃ P : ι → Polynomial (Polynomial ℝ), (∀ i, P i ≠ 0) ∧
        ∀ t : ℝ, r.eval t ≠ 0 →
          (∀ i, RootBranchCount.specialize (P i) t ≠ 0) ∧
          ∀ x : ι → ℝ, system q base u (t, x) = 0 →
            Function.Surjective (fderiv ℝ (fun y => q.eval₂ (Polynomial.evalRingHom t) y) x) →
            (PolynomialRootFamily.jacobian (ProjectionCriticalFamily.spatialEquation q base
              (normalizedDirection base (fun i => (u i : Polynomial ℝ))))).eval₂
                (Polynomial.evalRingHom t) x ≠ 0 ∧
              ∀ i, AlgebraicBranchLimit.value (P i) t (x i) = 0 := by
  let F := FractionRing (Polynomial ℝ)
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap ℝ F).injective
  obtain ⟨_, u, _, cert, r, hr, h⟩ := UniformCriticalSpecialization.exists_uniform (F := F) q base
  let v := normalizedDirection base (fun i => (u i : Polynomial ℝ))
  let P := fun i => Polynomial.Bivariate.swap (cert.polynomial (some i))
  have hP (i : ι) : P i ≠ 0 := by
    intro hz
    apply cert.polynomial_ne_zero (some i)
    apply Polynomial.Bivariate.swap.injective
    simpa only [P, map_zero] using hz
  refine ⟨u, r, hr, Polynomial.finite_setOfPred_isRoot hr, P, hP, ?_⟩
  intro t ht
  let φ := Polynomial.evalRingHom t
  have hs := h ℝ φ ht
  refine ⟨?_, ?_⟩
  · intro i
    change ((Polynomial.Bivariate.swap (Polynomial.Bivariate.swap (cert.polynomial (some i)))).map φ) ≠ 0
    rw [Polynomial.Bivariate.swap_swap_apply]
    exact hs.1 (some i)
  · intro x hx hregular
    have hv : φ (v base) = 1 := by simp [v, normalizedDirection, φ]
    have hrows : ∀ i, (ProjectionCriticalFamily.spatialEquation q base v i).eval₂ φ x = 0 :=
      fun i => congrFun hx i
    obtain ⟨hq, hpartial⟩ := (ProjectionCriticalFamily.spatial_zero_iff φ q base v hv x).mp hrows
    have hb : (pderiv base q).eval₂ φ x ≠ 0 := by
      intro hb
      have hall (i : ι) : (pderiv i q).eval₂ φ x = 0 := by rw [hpartial i, hb, mul_zero]
      have hzero := (PolynomialCalculus.critical_iff φ q x).mpr hall
      obtain ⟨y, hy⟩ := hregular 1
      rw [hzero] at hy
      exact zero_ne_one hy
    let z : Option ι → ℝ := fun i => i.elim ((pderiv base q).eval₂ φ x)⁻¹ x
    have hz : ∀ j, (ProjectionCriticalFamily.equation q base v j).eval₂ φ z = 0 := by
      apply (ProjectionCriticalFamily.equations_iff φ q base v z).mpr
      exact ⟨hq, inv_mul_cancel₀ hb, hpartial⟩
    have hgood := hs.2.2 z hz
    have hjac := hgood.1
    rw [ProjectionCriticalFamily.eval_jacobian, GenericProjectionJacobian.extended_det] at hjac
    refine ⟨?_, ?_⟩
    · change (ProjectionCriticalFamily.spatialJacobian q base v).eval₂ φ x ≠ 0
      rw [ProjectionCriticalFamily.eval_spatialJacobian]
      exact (mul_ne_zero_iff.mp hjac).1
    · intro i
      rw [← RootBranchCount.eval_specialize]
      change ((Polynomial.Bivariate.swap (Polynomial.Bivariate.swap (cert.polynomial (some i)))).map φ).eval (x i) = 0
      rw [Polynomial.Bivariate.swap_swap_apply]
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
        z, Option.elim_some] using hgood.2 (some i)

end LeanCanny.Geometry.ParameterizedCriticalBranches
