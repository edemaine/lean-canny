/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FiniteProjectionRoots
public import LeanCanny.Geometry.TubeCriticalSampling

/-! # Finite generic projection roots of the actual tubes

Specialize the tube coefficients through a characteristic-zero subfield of
the reals. If the non-base direction coordinates are independent over that
field, every regular tube level has finitely many expanded integer projection
roots. The common small-level regularity interval is already established.
This does not yet construct or effectively select the field or direction.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K] [Algebra K ℝ]

theorem finite_projectionRootSet_of_lift (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta alpha : ℝ)
    (ψ : Coefficient →+* K) (hψ : (algebraMap K ℝ).comp ψ = coefficientMap epsilon delta alpha)
    (v : Coordinate ι → ℝ) (hv : v (base ι) = 1)
    (hind : AlgebraicIndependent K (fun i : {i : Coordinate ι // i ≠ base ι} => v i))
    (hregular : ∀ x : Coordinate ι → ℝ,
      (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
        Function.Surjective (fderiv ℝ (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) x)) :
    (projectionRootSet p s epsilon delta alpha v).Finite := by
  have h := ProjectionCritical.finite_roots_of_coefficient_lift (coefficientMap epsilon delta alpha) ψ hψ
    (polynomial p s) (base ι) v hv hind hregular
  apply h.subset
  intro x hx j
  have hr := hx j
  rw [eval_integerProjection] at hr
  exact hr

theorem exists_generic_finite_roots_interval (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ (ψ : Coefficient →+* K), (algebraMap K ℝ).comp ψ = coefficientMap epsilon delta alpha →
        ∀ v : Coordinate ι → ℝ, v (base ι) = 1 →
          AlgebraicIndependent K (fun i : {i : Coordinate ι // i ≠ base ι} => v i) →
            ∀ s : Finset (PolynomialPerturbation.Constraint ι), (projectionRootSet p s epsilon delta alpha v).Finite := by
  obtain ⟨a, ha, hr⟩ := exists_common_regular_interval p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs ψ hψ v hv hind s
  exact finite_projectionRootSet_of_lift p s epsilon delta alpha ψ hψ v hv hind
    (fun x hx => hr alpha hp hs s x hx)

end LeanCanny.Geometry.TubePolynomial
