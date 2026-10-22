/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AsymmetricCoordinateRecovery
public import LeanCanny.Algebra.GaloisFixedPolynomial
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Descent of finite vector projection polynomials

Automorphisms permuting a finite vector set fix every nodal polynomial with
an equivariant node map, including asymmetric shifted projections. In a
Galois extension these polynomials therefore have coefficients in the base field.
A finite full zero set of base-field polynomial equations is stable as required.
-/

@[expose] public section

namespace LeanCanny.Algebra.VectorGaloisDescent

variable {ι K L : Type*} [Field K] [Field L] [Algebra K L]

def act (σ : L ≃ₐ[K] L) (x : ι → L) : ι → L := fun i => σ (x i)

def Stable (s : Finset (ι → L)) : Prop :=
  ∀ σ : L ≃ₐ[K] L, ∀ x ∈ s, act σ x ∈ s

@[simp] theorem act_apply_symm (σ : L ≃ₐ[K] L) (x : ι → L) : act σ (act σ.symm x) = x := by
  funext i
  exact σ.apply_symm_apply (x i)

theorem act_injective (σ : L ≃ₐ[K] L) : Function.Injective (act (ι := ι) σ) := by
  intro x y he
  funext i
  exact σ.injective (congrFun he i)

theorem nodal_fixed (s : Finset (ι → L)) (hs : Stable (K := K) s)
    (f : (ι → L) → L) (hf : ∀ (σ : L ≃ₐ[K] L) x, f (act σ x) = σ (f x))
    (σ : L ≃ₐ[K] L) :
    (Lagrange.nodal s f).map (σ : L →+* L) = Lagrange.nodal s f := by
  classical
  simp only [Lagrange.nodal, Polynomial.map_prod]
  apply Finset.prod_bij (fun x _ => act σ x)
  · exact fun x hx => hs σ x hx
  · exact fun _ _ _ _ h => act_injective σ h
  · intro y hy
    exact ⟨act σ.symm y, hs σ.symm y hy, act_apply_symm σ y⟩
  · intro x _
    simp [hf]

theorem eval_act (σ : L ≃ₐ[K] L) (p : MvPolynomial ι K) (x : ι → L) :
    MvPolynomial.eval₂ (algebraMap K L) (act σ x) p =
      σ (MvPolynomial.eval₂ (algebraMap K L) x p) := by
  have hmap : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L := by
    ext a
    exact σ.commutes a
  change MvPolynomial.eval₂ (algebraMap K L) (fun i => σ (x i)) p = _
  have he := MvPolynomial.eval₂_comp_left (σ : L →+* L) (algebraMap K L) x p
  rw [hmap] at he
  exact he.symm

/-- Full zero sets of equations over the base field are stable; a subset of
selected real solutions need not satisfy this hypothesis. -/
theorem stable_of_zero_set {τ : Type*} (p : τ → MvPolynomial ι K) (s : Finset (ι → L))
    (hs : ∀ x, x ∈ s ↔ ∀ j, MvPolynomial.eval₂ (algebraMap K L) x (p j) = 0) :
    Stable (K := K) s := by
  intro σ x hx
  apply (hs _).mpr
  intro j
  rw [eval_act, (hs x).mp hx j, map_zero]

section Projection
variable [Fintype ι]
open AsymmetricProjection

theorem projection_act (σ : L ≃ₐ[K] L) (c : ι → ℕ) (x : ι → L) :
    projection c (act σ x) = σ (projection c x) := by
  simp [projection, act]

theorem plus_act (σ : L ≃ₐ[K] L) (c : ι → ℕ) (k : ℕ) (j : ι) (x : ι → L) :
    plus c k j (act σ x) = σ (plus c k j x) := by
  simp [plus, projection_act, act]

theorem minus_act (σ : L ≃ₐ[K] L) (c : ι → ℕ) (j : ι) (x : ι → L) :
    minus c j (act σ x) = σ (minus c j x) := by
  simp [minus, projection_act, act]

variable [IsGalois K L]

theorem exists_projection_polynomial (s : Finset (ι → L)) (hs : Stable (K := K) s) (c : ι → ℕ) :
    ∃ q : Polynomial K, q.map (algebraMap K L) = Lagrange.nodal s (projection c) :=
  exists_polynomial_of_galois_fixed _ (nodal_fixed s hs _ (fun σ x => projection_act σ c x))

theorem exists_plus_polynomial (s : Finset (ι → L)) (hs : Stable (K := K) s)
    (c : ι → ℕ) (k : ℕ) (j : ι) :
    ∃ q : Polynomial K, q.map (algebraMap K L) = Lagrange.nodal s (plus c k j) :=
  exists_polynomial_of_galois_fixed _ (nodal_fixed s hs _ (fun σ x => plus_act σ c k j x))

theorem exists_minus_polynomial (s : Finset (ι → L)) (hs : Stable (K := K) s)
    (c : ι → ℕ) (j : ι) :
    ∃ q : Polynomial K, q.map (algebraMap K L) = Lagrange.nodal s (minus c j) :=
  exists_polynomial_of_galois_fixed _ (nodal_fixed s hs _ (fun σ x => minus_act σ c j x))

end Projection
end LeanCanny.Algebra.VectorGaloisDescent
