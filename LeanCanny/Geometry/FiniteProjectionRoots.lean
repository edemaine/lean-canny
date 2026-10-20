/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericProjectionFinite
public import LeanCanny.Geometry.ProjectionCritical

/-! # Finite projection systems on regular real hypersurfaces

On a regular hypersurface, normalized projection equations force the base
partial derivative to be nonzero. Algebraic generic-fiber finiteness therefore
applies to every root. Coefficients may be specialized through a smaller
characteristic-zero field over which the direction coordinates are independent.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open MvPolynomial

variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
theorem system_roots_iff (φ : R →+* ℝ) (p : MvPolynomial ι R) (base : ι) (x v : ι → ℝ)
    (hv : v base = 1) :
    (∀ j, (Algebra.ProjectionEquations.system p base j).eval₂ φ (Sum.elim x v) = 0) ↔
      p.eval₂ φ x = 0 ∧ ∀ i, (pderiv i p).eval₂ φ x = v i * (pderiv base p).eval₂ φ x := by
  constructor
  · intro h
    constructor
    · have h0 := h none
      change (Algebra.ProjectionEquations.polynomial p base none).eval₂ φ (Sum.elim x v) = 0 at h0
      rwa [Algebra.ProjectionEquations.eval_level] at h0
    · intro i
      by_cases hi : i = base
      · simp only [hi, hv, one_mul]
      · have hp := h (some ⟨i, hi⟩)
        change (Algebra.ProjectionEquations.polynomial p base (some i)).eval₂ φ (Sum.elim x v) = 0 at hp
        rw [Algebra.ProjectionEquations.eval_partial] at hp
        exact sub_eq_zero.mp hp
  · rintro ⟨hp, hpartial⟩ j
    cases j with
    | none => exact (Algebra.ProjectionEquations.eval_level p base φ x v).trans hp
    | some i =>
      change (Algebra.ProjectionEquations.polynomial p base (some i.val)).eval₂ φ (Sum.elim x v) = 0
      rw [Algebra.ProjectionEquations.eval_partial, hpartial i, sub_self]

theorem base_partial_ne_zero (φ : R →+* ℝ) (p : MvPolynomial ι R) (base : ι) (x v : ι → ℝ)
    (hpartial : ∀ i, (pderiv i p).eval₂ φ x = v i * (pderiv base p).eval₂ φ x)
    (hregular : Function.Surjective (fderiv ℝ (fun y => p.eval₂ φ y) x)) :
    (pderiv base p).eval₂ φ x ≠ 0 := by
  classical
  intro hbase
  have hgrad : ∀ i, (pderiv i p).eval₂ φ x = 0 := by
    intro i
    rw [hpartial i, hbase, mul_zero]
  have hD := (PolynomialCalculus.critical_iff φ p x).mpr hgrad
  obtain ⟨h, hh⟩ := hregular 1
  rw [hD, zero_apply] at hh
  exact zero_ne_one hh

section CoefficientField
variable {K : Type*} [Field K] [CharZero K] [Algebra K ℝ]

theorem finite_roots_of_independent_direction (p : MvPolynomial ι K) (base : ι) (v : ι → ℝ)
    (hv : v base = 1) (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i))
    (hregular : ∀ x : ι → ℝ, p.eval₂ (algebraMap K ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => p.eval₂ (algebraMap K ℝ) y) x)) :
    {x : ι → ℝ | ∀ j, (Algebra.ProjectionEquations.system p base j).eval₂ (algebraMap K ℝ) (Sum.elim x v) = 0}.Finite := by
  apply (Algebra.GenericProjectionFinite.finite_regular_projection_roots p base v hv hind).subset
  intro x hx
  obtain ⟨hp, hpartial⟩ := (system_roots_iff (algebraMap K ℝ) p base x v hv).mp hx
  exact ⟨hp, hpartial, base_partial_ne_zero (algebraMap K ℝ) p base x v hpartial (hregular x hp)⟩

theorem finite_roots_of_coefficient_lift (φ : R →+* ℝ) (ψ : R →+* K)
    (hφ : (algebraMap K ℝ).comp ψ = φ) (p : MvPolynomial ι R) (base : ι) (v : ι → ℝ)
    (hv : v base = 1) (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i))
    (hregular : ∀ x : ι → ℝ, p.eval₂ φ x = 0 → Function.Surjective (fderiv ℝ (fun y => p.eval₂ φ y) x)) :
    {x : ι → ℝ | ∀ j, (Algebra.ProjectionEquations.system p base j).eval₂ φ (Sum.elim x v) = 0}.Finite := by
  have heval (q : MvPolynomial ι R) (x : ι → ℝ) : (q.map ψ).eval₂ (algebraMap K ℝ) x = q.eval₂ φ x := by
    rw [eval₂_map, hφ]
  have hfun : (fun x : ι → ℝ => (p.map ψ).eval₂ (algebraMap K ℝ) x) = fun x => p.eval₂ φ x := funext (heval p)
  have hreg : ∀ x : ι → ℝ, (p.map ψ).eval₂ (algebraMap K ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => (p.map ψ).eval₂ (algebraMap K ℝ) y) x) := by
    intro x hx
    rw [heval] at hx
    rw [hfun]
    exact hregular x hx
  apply (finite_roots_of_independent_direction (p.map ψ) base v hv hind hreg).subset
  intro x hx
  obtain ⟨hp, hpartial⟩ := (system_roots_iff φ p base x v hv).mp hx
  apply (system_roots_iff (algebraMap K ℝ) (p.map ψ) base x v hv).mpr
  constructor
  · rwa [heval]
  · intro i
    simpa only [pderiv_map, heval] using hpartial i

end CoefficientField
end LeanCanny.Geometry.ProjectionCritical
