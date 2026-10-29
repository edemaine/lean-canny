/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalRegularity
public import LeanCanny.Geometry.TriangularPolynomialRegularity
public import LeanCanny.Geometry.PolynomialCalculus

/-! # Analytic meaning of flat affine-height critical stages

Freezing ancestral coordinates gives exactly the formal spatial Jacobian.
At a regular stage root the new multiplier is nonzero, and the chosen height
annihilates every tangent direction to the source and the old height slices.
No regularity of singular slice points is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineCriticalGeometry
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem matrix_det (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → ℝ) :
    (TriangularPolynomialSystem.spatialJacobian (row p s a b)).eval₂ φ z =
      (FlatAffineCriticalRegularity.matrix φ p s a b z).det := by
  change (eval₂Hom φ z) (Matrix.det _) = _
  rw [RingHom.map_det]
  rfl

theorem analytic_iff (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (y : Variables n → ℝ) :
    (fderiv ℝ (fun v => fun j => (row p s a b j).eval₂ φ (Sum.elim x v)) y).IsInvertible ↔
      (FlatAffineCriticalRegularity.matrix φ p s a b (Sum.elim x y)).det ≠ 0 := by
  have he : (fun v => fun j => (row p s a b j).eval₂ φ (Sum.elim x v)) =
      (fun v => fun j => (TriangularPolynomialRegularity.freeze φ x (row p s a b j)).eval₂ (RingHom.id ℝ) v) := by
    funext v j
    exact (TriangularPolynomialRegularity.eval_freeze φ x v (row p s a b j)).symm
  rw [he, PolynomialSystemRegularity.isInvertible_iff]
  have hm := TriangularPolynomialRegularity.eval_spatialJacobian φ (row p s a b) x y
  rw [matrix_det] at hm
  exact Iff.of_eq (congrArg (fun t : ℝ => t ≠ 0) hm.symm)

theorem multiplier_ne_zero (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (y : Variables n → ℝ)
    (hr : ∀ j, (row p s a b j).eval₂ φ (Sum.elim x y) = 0)
    (hregular : (fderiv ℝ (fun v => fun j => (row p s a b j).eval₂ φ (Sum.elim x v)) y).IsInvertible) :
    y (Sum.inr 0) ≠ 0 :=
  FlatAffineCriticalRegularity.multiplier_ne_zero φ p s a b (Sum.elim x y) hr
    ((analytic_iff φ p s a b x y).mp hregular)

theorem critical_tangent (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (y : Variables n → ℝ)
    (hr : ∀ j, (row p s a b j).eval₂ φ (Sum.elim x y) = 0)
    (hregular : (fderiv ℝ (fun v => fun j => (row p s a b j).eval₂ φ (Sum.elim x v)) y).IsInvertible)
    (d : Fin n → ℝ)
    (hp : fderiv ℝ (fun v => p.eval₂ φ v) (fun i => y (Sum.inl i)) d = 0)
    (ha : ∀ j ∈ s, ∑ i, φ (a j.succ i) * d i = 0) : ∑ i, φ (a 0 i) * d i = 0 := by
  apply FlatAffineCriticalRegularity.tangent_height_zero φ p s a b (Sum.elim x y) hr
    ((analytic_iff φ p s a b x y).mp hregular) d ?_ ha
  rw [PolynomialCalculus.fderiv_eq, PolynomialCalculus.derivative_apply] at hp
  exact hp

end LeanCanny.Geometry.FlatAffineCriticalGeometry
