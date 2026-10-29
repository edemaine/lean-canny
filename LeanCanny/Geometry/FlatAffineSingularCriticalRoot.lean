/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineCriticalExtremum
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Critical stage roots at singular affine slices

Independent height normals make any dependence among the source and height
constraints have a nonzero source coefficient. Normalizing that dependence
gives the original Lagrange rows with objective multiplier zero. At a local
maximum, the regular and singular cases therefore both give stage roots.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSingularCriticalRoot
open LeanCanny.Algebra MvPolynomial
open FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem exists_stage_root_of_singular (phi : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ phi z = 0)
    (hl : ∀ j ∈ s, ∑ i, phi (a j.succ i) * z i = (b j).eval₂ phi x)
    (hindependent : ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * phi (a j.val.succ i) = 0) → ∀ j, c j = 0)
    (hsingular : ¬Function.Surjective (derivative phi p s a z)) :
    ∃ mu : Fin (n + 1) → ℝ, mu 0 = 0 ∧
      ∀ i, (row p s a b i).eval₂ phi (Sum.elim x (Sum.elim z mu)) = 0 := by
  let T := (derivative phi p s a z).toLinearMap
  have hr : LinearMap.range T < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, LinearMap.range_eq_top]
    exact hsingular
  obtain ⟨f, hf, hker⟩ := (LinearMap.range T).exists_le_ker_of_lt_top hr
  have hdual (v : Option s → ℝ) : f v = ∑ j, f (Pi.single j 1) * v j := by
    calc
      _ = f (∑ j, v j • Pi.single j 1) := congrArg f (pi_eq_sum_univ' v)
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_smul, smul_eq_mul, mul_comm]
  let c : Option s → ℝ := fun j => f (Pi.single j 1)
  have hc (i : Fin n) : c none * (pderiv i p).eval₂ phi z +
      ∑ j : s, c (some j) * phi (a j.val.succ i) = 0 := by
    have H : f (T (Pi.single i 1)) = 0 := hker ⟨Pi.single i 1, rfl⟩
    rw [hdual, Fintype.sum_option] at H
    simpa only [T, derivative, ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply,
      PolynomialCalculus.derivative_single, constraint, height_partial, c] using H
  have hcn : c none ≠ 0 := by
    intro he
    have hz : ∀ j : s, c (some j) = 0 := hindependent _ (fun i => by simpa only [he, zero_mul, zero_add] using hc i)
    apply hf
    apply LinearMap.ext
    intro v
    change f v = 0
    rw [hdual, Fintype.sum_option]
    change c none * v none + (∑ j : s, c (some j) * v (some j)) = 0
    simp only [he, hz, zero_mul, Finset.sum_const_zero, add_zero]
  let mu : Fin (n + 1) → ℝ := Fin.cases 0
    (fun j => if hj : j ∈ s then -(c none)⁻¹ * c (some ⟨j, hj⟩) else 0)
  refine ⟨mu, rfl, (roots_iff phi p s a b _).mpr ⟨hp, hl, ?_, ?_⟩⟩
  · intro i
    have hsum : (∑ j : Fin n, phi (a j.succ i) * mu j.succ) =
        -(c none)⁻¹ * ∑ j : s, c (some j) * phi (a j.val.succ i) := by
      have hs : (∑ j : Fin n, phi (a j.succ i) * mu j.succ) =
          ∑ j ∈ s, phi (a j.succ i) * mu j.succ := by
        apply (Finset.sum_subset (Finset.subset_univ s) ?_).symm
        intro j _ hj
        simp only [mu, Fin.cases_succ, dite_eq_right hj, mul_zero]
      rw [hs, ← Finset.sum_attach s (fun j => phi (a j.succ i) * mu j.succ)]
      change (∑ j : s, phi (a j.val.succ i) * mu j.val.succ) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mu, Fin.cases_succ, dite_eq_left j.property]
      ring
    change (pderiv i p).eval₂ phi z = ∑ j, phi (a j i) * mu j
    rw [Fin.sum_univ_succ, hsum]
    simp only [mu, Fin.cases_zero, mul_zero, zero_add]
    have H := hc i
    field_simp
    nlinarith
  · intro j hj
    change mu j.succ = 0
    simp only [mu, Fin.cases_succ, dite_eq_right hj]

/-- Slice maxima give original roots even when the constraint derivative is
singular. Only the height normals and the new objective need independence. -/
theorem exists_stage_root_at_max (phi : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ phi z = 0)
    (hl : ∀ j ∈ s, ∑ i, phi (a j.succ i) * z i = (b j).eval₂ phi x)
    (hmax : IsLocalMaxOn (ProjectionCritical.projection (fun i => phi (a 0 i)))
      {y | p.eval₂ phi y = 0 ∧ ∀ j ∈ s, ∑ i, phi (a j.succ i) * y i = (b j).eval₂ phi x} z)
    (hheights : ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * phi (a j.val.succ i) = 0) → ∀ j, c j = 0)
    (hobjective : ¬∃ c : s → ℝ, ∀ i, phi (a 0 i) = ∑ j : s, c j * phi (a j.val.succ i)) :
    ∃ mu : Fin (n + 1) → ℝ, ∀ i, (row p s a b i).eval₂ phi (Sum.elim x (Sum.elim z mu)) = 0 := by
  by_cases hregular : Function.Surjective (derivative phi p s a z)
  · obtain ⟨mu, _, hmu⟩ := FlatAffineCriticalExtremum.exists_stage_root_on_slice phi p s a b x z
      hp hl hmax hregular hobjective
    exact ⟨mu, hmu⟩
  · obtain ⟨mu, _, hmu⟩ := exists_stage_root_of_singular phi p s a b x z hp hl hheights hregular
    exact ⟨mu, hmu⟩

end LeanCanny.Geometry.FlatAffineSingularCriticalRoot
