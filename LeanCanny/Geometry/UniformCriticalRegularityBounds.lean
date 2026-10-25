/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedCriticalCoordinates
public import LeanCanny.Geometry.PolynomialCalculus
public import LeanCanny.Algebra.UniformCriticalSpecialization

/-! # Bounded regularity factors for one uniform integer critical direction

Choose a direction using the generic field construction. A qualitative factor
for regular original slices suffices to construct a bounded factor excluding
all singular spatial critical roots. The direction allowance remains
existential; its input-size bound is a separate obligation.
-/

@[expose] public section
namespace LeanCanny.Geometry.UniformCriticalRegularityBounds
open scoped Classical
open MvPolynomial LeanCanny.Algebra ProjectionFiniteSpecialization
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_bounded (q : MvPolynomial (Fin n) (Polynomial ℤ)) (base : Fin n) (D E b : ℕ)
    (hD : q.totalDegree ≤ D) (hdegree : ∀ e, (q.coeff e).natDegree ≤ E)
    (hmass : ∀ e, coefficientMass (q.coeff e) ≤ 2 ^ b)
    (a : Polynomial ℤ) (ha : a ≠ 0)
    (hregular : ∀ (t : ℝ), a.eval₂ (Int.castRingHom ℝ) t ≠ 0 → ∀ x : Fin n → ℝ,
      q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x = 0 →
      Function.Surjective (fderiv ℝ
        (fun y => q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) y) x)) :
    ∃ U : ℕ, ∃ v : Fin n → ℕ, v base = 1 ∧ (∀ i, v i ≤ U) ∧
      ∃ r : Polynomial ℤ, r ≠ 0 ∧ r.natDegree ≤ ParameterizedSingularityBounds.degreeBound n D E ∧
        coefficientMass r < 2 ^ ParameterizedSingularityBounds.massExponent n D E
          (ProjectionCriticalBounds.massExponent b D U) ∧
        ∀ (t : ℝ) (x : Fin n → ℝ),
          (∀ j, (ProjectionCriticalFamily.spatialEquation q base (fun i => (v i : Polynomial ℤ)) j).eval₂
            (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x = 0) →
          r.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
            (ProjectionCriticalFamily.spatialJacobian q base (fun i => (v i : Polynomial ℤ))).eval₂
              (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x ≠ 0 := by
  let F := FractionRing (Polynomial ℤ)
  let : CharZero F := charZero_of_injective_algebraMap
    (IsFractionRing.injective (Polynomial ℤ) F)
  obtain ⟨B, u, hu, _cert, d, hd, hgood⟩ :=
    UniformCriticalSpecialization.exists_uniform (F := F) q base
  let v : Fin n → ℕ := normalizedDirection base u
  let vA := normalizedDirection base (fun i => (u i : Polynomial ℤ))
  have hva : (fun i => (v i : Polynomial ℤ)) = vA := by
    funext i
    simp only [v, vA, normalizedDirection]
    split_ifs <;> simp
  have hU (i : Fin n) : v i ≤ max 1 B := by
    dsimp only [v, normalizedDirection]
    split_ifs
    · exact le_max_left _ _
    · exact (hu _).trans (le_max_right _ _)
  have hd0 : d * a ≠ 0 := mul_ne_zero hd ha
  have hgeneric (t : ℝ) (x : Fin n → ℝ)
      (hrows : ∀ j, (ProjectionCriticalFamily.spatialEquation q base
        (fun i => (v i : Polynomial ℤ)) j).eval₂
          (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x = 0)
      (ht : (d * a).eval₂ (Int.castRingHom ℝ) t ≠ 0) :
      (ProjectionCriticalFamily.spatialJacobian q base (fun i => (v i : Polynomial ℤ))).eval₂
        (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x ≠ 0 := by
    let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) t
    have hfac : d.eval₂ (Int.castRingHom ℝ) t ≠ 0 ∧ a.eval₂ (Int.castRingHom ℝ) t ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [Polynomial.eval₂_mul] using ht)
    have hv : φ (vA base) = 1 := by simp [φ, vA, normalizedDirection]
    rw [hva] at hrows ⊢
    obtain ⟨hq, hpartial⟩ := (ProjectionCriticalFamily.spatial_zero_iff φ q base vA hv x).mp hrows
    have hb : (pderiv base q).eval₂ φ x ≠ 0 := by
      intro hb
      have hall (i : Fin n) : (pderiv i q).eval₂ φ x = 0 := by rw [hpartial i, hb, mul_zero]
      have hzero := (PolynomialCalculus.critical_iff φ q x).mpr hall
      obtain ⟨y, hy⟩ := hregular t hfac.2 x hq 1
      rw [hzero] at hy
      exact zero_ne_one hy
    let z : Option (Fin n) → ℝ := fun i => i.elim ((pderiv base q).eval₂ φ x)⁻¹ x
    have hz : ∀ j, (ProjectionCriticalFamily.equation q base vA j).eval₂ φ z = 0 :=
      (ProjectionCriticalFamily.equations_iff φ q base vA z).mpr ⟨hq, inv_mul_cancel₀ hb, hpartial⟩
    have hjac := (hgood ℝ φ hfac.1).2.2 z hz |>.1
    rw [ProjectionCriticalFamily.eval_jacobian, GenericProjectionJacobian.extended_det] at hjac
    change (ProjectionCriticalFamily.spatialJacobian q base vA).eval₂ φ x ≠ 0
    rw [ProjectionCriticalFamily.eval_spatialJacobian]
    exact (mul_ne_zero_iff.mp hjac).1
  obtain ⟨r, hr, hrD, hrM, hrregular⟩ := BoundedCriticalCoordinates.exists_bounded_regularity q base v
    D (max 1 B) E b hD hU hdegree hmass (d * a) hd0 hgeneric
  exact ⟨max 1 B, v, by simp [v, normalizedDirection], hU, r, hr, hrD, hrM, hrregular⟩

end LeanCanny.Geometry.UniformCriticalRegularityBounds
