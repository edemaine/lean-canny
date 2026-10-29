/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineCriticalGeometry
public import LeanCanny.Geometry.ProjectionCritical
import Mathlib.Tactic.FieldSimp

/-! # Constrained height extrema yield flat critical stage roots

The source equation and active old heights form the constraint map. At a
regular constrained maximum, normalized Lagrange multipliers express the new
height in their span. Independence from the old heights makes the source
coefficient nonzero, allowing normalization to the stage's gradient equations.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineCriticalExtremum
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} {n : ℕ} [CommRing R]

noncomputable def constraint (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) : Option s → MvPolynomial (Fin n) R
  | none => p
  | some j => AffineHeightPolynomial.polynomial (a j.val.succ) id

noncomputable def derivative (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (z : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Option s → ℝ) :=
  ContinuousLinearMap.pi (fun j => PolynomialCalculus.derivative φ (constraint p s a j) z)

theorem height_partial (φ : R →+* ℝ) (a : Fin n → R) (z : Fin n → ℝ) (i : Fin n) :
    (pderiv i (AffineHeightPolynomial.polynomial a id)).eval₂ φ z = φ (a i) := by
  simp [AffineHeightPolynomial.polynomial, pderiv_X, Pi.single_apply]

theorem exists_coefficients (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (z : Fin n → ℝ)
    (hmax : IsLocalMaxOn (ProjectionCritical.projection (fun i => φ (a 0 i)))
      {y | (fun j => (constraint p s a j).eval₂ φ y) =
        (fun j => (constraint p s a j).eval₂ φ z)} z)
    (hregular : Function.Surjective (derivative φ p s a z)) :
    ∃ c : Option s → ℝ, ∀ i, φ (a 0 i) = c none * (pderiv i p).eval₂ φ z +
      ∑ j : s, c (some j) * φ (a j.val.succ i) := by
  have hd : HasStrictFDerivAt (fun y j => (constraint p s a j).eval₂ φ y)
      (derivative φ p s a z) z := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    simpa only [PolynomialCalculus.fderiv_eq] using
      (ProjectionCritical.contDiff_eval φ (constraint p s a j)).hasStrictFDerivAt (x := z) (by simp)
  obtain ⟨Λ, hΛ⟩ := ActiveExtremum.exists_normalized _ _ z _ _ hmax hd
    (ProjectionCritical.projection (fun i => φ (a 0 i))).hasStrictFDerivAt hregular
  have hdual (v : Option s → ℝ) : Λ v = ∑ j, Λ (Pi.single j 1) * v j := by
    calc
      _ = Λ (∑ j, v j • Pi.single j 1) := congrArg Λ (pi_eq_sum_univ' v)
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun j => Λ (Pi.single j 1), fun i => ?_⟩
  have hi := hΛ (Pi.single i 1)
  rw [ProjectionCritical.projection_single, hdual, Fintype.sum_option] at hi
  simpa only [derivative, ContinuousLinearMap.pi_apply, PolynomialCalculus.derivative_single,
    constraint, height_partial] using hi

theorem exists_stage_root (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ φ z = 0)
    (hl : ∀ j ∈ s, ∑ i, φ (a j.succ i) * z i = (b j).eval₂ φ x)
    (hmax : IsLocalMaxOn (ProjectionCritical.projection (fun i => φ (a 0 i)))
      {y | (fun j => (constraint p s a j).eval₂ φ y) =
        (fun j => (constraint p s a j).eval₂ φ z)} z)
    (hregular : Function.Surjective (derivative φ p s a z))
    (hindependent : ¬ ∃ c : s → ℝ, ∀ i, φ (a 0 i) = ∑ j : s, c j * φ (a j.val.succ i)) :
    ∃ μ : Fin (n + 1) → ℝ, μ 0 ≠ 0 ∧
      ∀ j, (row p s a b j).eval₂ φ (Sum.elim x (Sum.elim z μ)) = 0 := by
  obtain ⟨c, hc⟩ := exists_coefficients φ p s a z hmax hregular
  have hcn : c none ≠ 0 := by
    intro he
    apply hindependent
    refine ⟨fun j => c (some j), fun i => ?_⟩
    simpa only [he, zero_mul, zero_add] using hc i
  let μ : Fin (n + 1) → ℝ := Fin.cases (c none)⁻¹
    (fun j => if hj : j ∈ s then -(c none)⁻¹ * c (some ⟨j, hj⟩) else 0)
  refine ⟨μ, inv_ne_zero hcn, (roots_iff φ p s a b _).mpr ⟨hp, hl, ?_, ?_⟩⟩
  · intro i
    have hsum : (∑ j : Fin n, φ (a j.succ i) * μ j.succ) =
        -(c none)⁻¹ * ∑ j : s, c (some j) * φ (a j.val.succ i) := by
      have hs : (∑ j : Fin n, φ (a j.succ i) * μ j.succ) =
          ∑ j ∈ s, φ (a j.succ i) * μ j.succ := by
        apply (Finset.sum_subset (Finset.subset_univ s) ?_).symm
        intro j _ hj
        simp only [μ, Fin.cases_succ, dite_eq_right hj, mul_zero]
      rw [hs, ← Finset.sum_attach s (fun j => φ (a j.succ i) * μ j.succ)]
      change (∑ j : s, φ (a j.val.succ i) * μ j.val.succ) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [μ, Fin.cases_succ, dite_eq_left j.property]
      ring
    change (pderiv i p).eval₂ φ z = ∑ j, φ (a j i) * μ j
    rw [Fin.sum_univ_succ, hsum]
    have he := hc i
    dsimp only [μ, Fin.cases_zero]
    field_simp
    nlinarith
  · intro j hj
    change μ j.succ = 0
    simp only [μ, Fin.cases_succ, dite_eq_right hj]

/-- The analytic fiber is the actual affine slice at a feasible point. -/
theorem fiber_eq_slice (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ φ z = 0)
    (hl : ∀ j ∈ s, ∑ i, φ (a j.succ i) * z i = (b j).eval₂ φ x) :
    {y | (fun j => (constraint p s a j).eval₂ φ y) =
      (fun j => (constraint p s a j).eval₂ φ z)} =
    {y | p.eval₂ φ y = 0 ∧ ∀ j ∈ s, ∑ i, φ (a j.succ i) * y i = (b j).eval₂ φ x} := by
  ext y
  constructor
  · intro he
    refine ⟨(congrFun he none).trans hp, ?_⟩
    intro j hj
    have hh := congrFun he (some ⟨j, hj⟩)
    simp only [constraint, AffineHeightPolynomial.eval, id_eq] at hh
    exact hh.trans (hl j hj)
  · rintro ⟨hy, hh⟩
    funext j
    cases j with
    | none => exact hy.trans hp.symm
    | some j =>
      simp only [constraint, AffineHeightPolynomial.eval, id_eq]
      exact (hh j.val j.property).trans (hl j.val j.property).symm

theorem exists_stage_root_on_slice (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ φ z = 0)
    (hl : ∀ j ∈ s, ∑ i, φ (a j.succ i) * z i = (b j).eval₂ φ x)
    (hmax : IsLocalMaxOn (ProjectionCritical.projection (fun i => φ (a 0 i)))
      {y | p.eval₂ φ y = 0 ∧ ∀ j ∈ s, ∑ i, φ (a j.succ i) * y i = (b j).eval₂ φ x} z)
    (hregular : Function.Surjective (derivative φ p s a z))
    (hindependent : ¬ ∃ c : s → ℝ, ∀ i, φ (a 0 i) = ∑ j : s, c j * φ (a j.val.succ i)) :
    ∃ μ : Fin (n + 1) → ℝ, μ 0 ≠ 0 ∧
      ∀ j, (row p s a b j).eval₂ φ (Sum.elim x (Sum.elim z μ)) = 0 := by
  apply exists_stage_root φ p s a b x z hp hl ?_ hregular hindependent
  rwa [fiber_eq_slice φ p s a b x z hp hl]

/-- A doubled current height equated to two ancestral heights lies strictly
between them. Ambient coordinates need not be coordinatewise midpoints. -/
theorem midpoint_between (φ : R →+* ℝ) (a : Fin n → R)
    (left right current : Fin n → ι) (z : ι → ℝ)
    (hr : (AffineHeightPolynomial.polynomial (fun i => 2 * a i) current -
      AffineHeightPolynomial.midpointLevel a left right).eval₂ φ z = 0)
    (hlt : (∑ i, φ (a i) * z (left i)) < ∑ i, φ (a i) * z (right i)) :
    (∑ i, φ (a i) * z (left i)) < (∑ i, φ (a i) * z (current i)) ∧
      (∑ i, φ (a i) * z (current i)) < ∑ i, φ (a i) * z (right i) := by
  have he := (AffineHeightPolynomial.midpoint_equation φ a left right current z).mp hr
  constructor <;> linarith

end LeanCanny.Geometry.FlatAffineCriticalExtremum
