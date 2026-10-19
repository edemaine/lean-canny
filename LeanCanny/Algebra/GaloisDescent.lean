/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Separation
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Descent of separating-coordinate polynomials to the input field

In a finite Galois extension, a finite set of points stable under every base-field
automorphism has its nodal polynomial and coordinate interpolants over the base
field. This supplies the coefficient-field part of Canny's Lemma 2.1. The proof
uses uniqueness of interpolation and Galois fixed points; it does not supply the
report's effective resultant/subresultant computation or its workspace bound.
-/

@[expose] public section

namespace LeanCanny.Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply an input-field automorphism to both coordinates. -/
def actPoint (σ : L ≃ₐ[K] L) (p : L × L) : L × L := (σ p.1, σ p.2)

@[simp] theorem actPoint_apply_symm (σ : L ≃ₐ[K] L) (p : L × L) :
    actPoint σ (actPoint σ.symm p) = p := by
  simp [actPoint]

@[simp] theorem shear_actPoint (σ : L ≃ₐ[K] L) (c : ℕ) (p : L × L) :
    shear c (actPoint σ p) = σ (shear c p) := by
  simp [shear, actPoint]

/-- Closure under all automorphisms fixing the input coefficient field. -/
def GaloisStable (s : Finset (L × L)) : Prop :=
  ∀ σ : L ≃ₐ[K] L, ∀ p ∈ s, actPoint σ p ∈ s

theorem eval_map_at_shear (σ : L ≃ₐ[K] L) (c : ℕ) (g : Polynomial L) (p : L × L) :
    (g.map (σ : L →+* L)).eval (shear c p) = σ (g.eval (shear c (actPoint σ.symm p))) := by
  have h : σ (shear c (actPoint σ.symm p)) = shear c p := by
    rw [← shear_actPoint, actPoint_apply_symm]
  rw [← h]
  simpa using (Polynomial.eval_map_apply (f := (σ : L →+* L)) (p := g)
    (shear c (actPoint σ.symm p)))

/-- An automorphism permuting the points fixes their monic nodal polynomial. -/
theorem nodal_fixed (s : Finset (L × L)) (hs : GaloisStable (K := K) s)
    (c : ℕ) (hinj : Set.InjOn (shear c) (s : Set (L × L))) (σ : L ≃ₐ[K] L) :
    (Lagrange.nodal s (shear c)).map (σ : L →+* L) = Lagrange.nodal s (shear c) := by
  classical
  have hm : (Lagrange.nodal s (shear c)).Monic := Lagrange.nodal_monic
  apply Polynomial.eq_of_degree_le_of_eval_index_eq s hinj
  · simp only [Polynomial.degree_map, Lagrange.degree_nodal]
    exact le_rfl
  · exact Polynomial.degree_map _ _
  · simp only [Polynomial.leadingCoeff_map, hm.leadingCoeff, map_one]
  · intro p hp
    rw [eval_map_at_shear, Lagrange.eval_nodal_at_node (hs σ.symm p hp),
      Lagrange.eval_nodal_at_node hp, map_zero]

/-- Uniqueness of interpolation forces equivariant value data to have fixed coefficients. -/
theorem interpolate_fixed [DecidableEq (L × L)] (s : Finset (L × L)) (hs : GaloisStable (K := K) s)
    (c : ℕ) (hinj : Set.InjOn (shear c) (s : Set (L × L)))
    (r : L × L → L) (hr : ∀ (σ : L ≃ₐ[K] L) p, r (actPoint σ p) = σ (r p))
    (σ : L ≃ₐ[K] L) :
    (Lagrange.interpolate s (shear c) r).map (σ : L →+* L) = Lagrange.interpolate s (shear c) r := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq s hinj
  · rw [Polynomial.degree_map]
    exact Lagrange.degree_interpolate_lt _ hinj
  · exact Lagrange.degree_interpolate_lt _ hinj
  · intro p hp
    rw [eval_map_at_shear, Lagrange.eval_interpolate_at_node r hinj (hs σ.symm p hp),
      Lagrange.eval_interpolate_at_node r hinj hp, hr]
    exact σ.apply_symm_apply _

section FiniteGalois
variable [FiniteDimensional K L] [IsGalois K L]

/-- A polynomial fixed coefficientwise by every base-field automorphism descends. -/
theorem exists_polynomial_of_fixed (g : Polynomial L)
    (hg : ∀ σ : L ≃ₐ[K] L, g.map (σ : L →+* L) = g) :
    ∃ q : Polynomial K, q.map (algebraMap K L) = g := by
  apply (Polynomial.mem_lifts g).mp
  apply (Polynomial.lifts_iff_coeff_lifts g).mpr
  intro n
  apply (IsGalois.mem_range_algebraMap_iff_fixed (g.coeff n)).mpr
  intro σ
  have h := congrArg (fun p : Polynomial L => p.coeff n) (hg σ)
  simpa using h

variable [CharZero L]

/-- Finite Galois-stable point sets have degree-bounded univariate coordinates
with coefficients in the input field, and the nodal polynomial has no extra roots. -/
theorem exists_univariate_coordinates_over_base (s : Finset (L × L))
    (hs : GaloisStable (K := K) s) :
    ∃ (c : ℕ) (q r₁ r₂ : Polynomial K),
      c ≤ s.card ^ 2 ∧ Set.InjOn (shear c) (s : Set (L × L)) ∧
      q.Monic ∧ q.Separable ∧ q.natDegree = s.card ∧
      r₁.degree < (s.card : WithBot ℕ) ∧ r₂.degree < (s.card : WithBot ℕ) ∧
      (∀ θ : L, Polynomial.aeval θ q = 0 ↔ ∃ p ∈ s, θ = shear c p) ∧
      ∀ p ∈ s, Polynomial.aeval (shear c p) r₁ = p.1 ∧ Polynomial.aeval (shear c p) r₂ = p.2 := by
  classical
  obtain ⟨c, hc, hinj⟩ := exists_bounded_separating_shear s
  obtain ⟨q, hq⟩ := exists_polynomial_of_fixed (Lagrange.nodal s (shear c)) (nodal_fixed s hs c hinj)
  obtain ⟨r₁, hr₁⟩ := exists_polynomial_of_fixed (Lagrange.interpolate s (shear c) Prod.fst)
    (interpolate_fixed s hs c hinj Prod.fst (by intros; rfl))
  obtain ⟨r₂, hr₂⟩ := exists_polynomial_of_fixed (Lagrange.interpolate s (shear c) Prod.snd)
    (interpolate_fixed s hs c hinj Prod.snd (by intros; rfl))
  refine ⟨c, q, r₁, r₂, hc, hinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Polynomial.monic_of_injective (algebraMap K L).injective
    rw [hq]
    exact Lagrange.nodal_monic
  · apply (Polynomial.separable_map (algebraMap K L)).mp
    rw [hq, Lagrange.nodal]
    exact Polynomial.separable_prod_X_sub_C_iff'.mpr hinj
  · rw [← Polynomial.natDegree_map (algebraMap K L), hq, Lagrange.natDegree_nodal]
  · rw [← Polynomial.degree_map r₁ (algebraMap K L), hr₁]
    exact Lagrange.degree_interpolate_lt _ hinj
  · rw [← Polynomial.degree_map r₂ (algebraMap K L), hr₂]
    exact Lagrange.degree_interpolate_lt _ hinj
  · intro θ
    rw [← Polynomial.eval_map_algebraMap, hq, Lagrange.eval_nodal, Finset.prod_eq_zero_iff]
    simp only [sub_eq_zero]
  · intro p hp
    rw [← Polynomial.eval_map_algebraMap, hr₁, ← Polynomial.eval_map_algebraMap, hr₂]
    exact ⟨Lagrange.eval_interpolate_at_node _ hinj hp, Lagrange.eval_interpolate_at_node _ hinj hp⟩

end FiniteGalois
end LeanCanny.Algebra
