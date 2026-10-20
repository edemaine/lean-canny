/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionFiniteSpecialization
public import LeanCanny.Geometry.FiniteProjectionRoots

/-! # Integer normalized directions with finite regular projection roots

A finite family of regular real hypersurfaces has a common normalized
direction whose non-base coordinates are natural numbers and whose projection
root sets are all finite. Exceptional polynomials give a finite candidate
grid, but no input-size bound on that grid is yet supplied.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open MvPolynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
theorem system_eval_map (φ : R →+* ℝ) (p : MvPolynomial ι R) (base : ι) (x v : ι → ℝ)
    (j : Algebra.ProjectionEquations.Index base) :
    (Algebra.ProjectionEquations.system (p.map φ) base j).eval₂ (RingHom.id ℝ) (Sum.elim x v) =
      (Algebra.ProjectionEquations.system p base j).eval₂ φ (Sum.elim x v) := by
  cases j with
  | none =>
    change (Algebra.ProjectionEquations.polynomial (p.map φ) base none).eval₂ _ _ =
      (Algebra.ProjectionEquations.polynomial p base none).eval₂ _ _
    rw [Algebra.ProjectionEquations.eval_level, Algebra.ProjectionEquations.eval_level,
      eval₂_map, RingHom.id_comp]
  | some i =>
    change (Algebra.ProjectionEquations.polynomial (p.map φ) base (some i.val)).eval₂ _ _ =
      (Algebra.ProjectionEquations.polynomial p base (some i.val)).eval₂ _ _
    rw [Algebra.ProjectionEquations.eval_partial, Algebra.ProjectionEquations.eval_partial,
      pderiv_map, pderiv_map, eval₂_map, eval₂_map, RingHom.id_comp]

theorem finite_roots_of_extended (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (hv : v base = 1)
    (hfinite : {z : Option ι → ℝ | ∀ j, MvPolynomial.aeval z
      (Algebra.GenericProjectionFinite.equation p base v j) = 0}.Finite)
    (hregular : ∀ x : ι → ℝ, p.eval₂ (RingHom.id ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => p.eval₂ (RingHom.id ℝ) y) x)) :
    {x : ι → ℝ | ∀ j, (Algebra.ProjectionEquations.system p base j).eval₂
      (RingHom.id ℝ) (Sum.elim x v) = 0}.Finite := by
  apply (Algebra.GenericProjectionFinite.finite_regular_projection_roots_of_extended p base v hfinite).subset
  intro x hx
  obtain ⟨hp, hpartial⟩ := (system_roots_iff (RingHom.id ℝ) p base x v hv).mp hx
  exact ⟨hp, hpartial, base_partial_ne_zero (RingHom.id ℝ) p base x v hpartial (hregular x hp)⟩

theorem exists_common_nat_direction {σ : Type*} [Fintype σ] (p : σ → MvPolynomial ι ℝ) (base : ι)
    (hregular : ∀ j (x : ι → ℝ), (p j).eval₂ (RingHom.id ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => (p j).eval₂ (RingHom.id ℝ) y) x)) :
    ∃ b : ℕ, ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      ∀ j, {x : ι → ℝ | ∀ k, (Algebra.ProjectionEquations.system (p j) base k).eval₂ (RingHom.id ℝ)
        (Sum.elim x (Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ)))) = 0}.Finite := by
  classical
  choose d hd hfinite using fun j => Algebra.ProjectionFiniteSpecialization.exists_exceptional_polynomial (p j) base
  obtain ⟨u, hu, he⟩ := Algebra.PolynomialGridAvoidance.exists_nat_common_nonzero d hd
    (∑ j, (d j).totalDegree) le_rfl
  let v := Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
  have hv : v base = 1 := by simp [v, Algebra.ProjectionFiniteSpecialization.normalizedDirection]
  refine ⟨∑ j, (d j).totalDegree, u, hu, ?_⟩
  intro j
  apply finite_roots_of_extended (p j) base v hv ?_ (hregular j)
  apply hfinite j ℝ (fun i => (u i : ℝ))
  exact he j

theorem exists_common_nat_direction_of_coefficients {σ : Type*} [Fintype σ]
    (φ : R →+* ℝ) (p : σ → MvPolynomial ι R) (base : ι)
    (hregular : ∀ j (x : ι → ℝ), (p j).eval₂ φ x = 0 →
      Function.Surjective (fderiv ℝ (fun y => (p j).eval₂ φ y) x)) :
    ∃ b : ℕ, ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      ∀ j, {x : ι → ℝ | ∀ k, (Algebra.ProjectionEquations.system (p j) base k).eval₂ φ
        (Sum.elim x (Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ)))) = 0}.Finite := by
  have heval (q : MvPolynomial ι R) (x : ι → ℝ) : (q.map φ).eval₂ (RingHom.id ℝ) x = q.eval₂ φ x := by
    rw [eval₂_map, RingHom.id_comp]
  have hreg : ∀ j (x : ι → ℝ), ((p j).map φ).eval₂ (RingHom.id ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => ((p j).map φ).eval₂ (RingHom.id ℝ) y) x) := by
    intro j x hx
    rw [heval] at hx
    have hfun : (fun y : ι → ℝ => ((p j).map φ).eval₂ (RingHom.id ℝ) y) = fun y => (p j).eval₂ φ y :=
      funext (heval (p j))
    rw [hfun]
    exact hregular j x hx
  obtain ⟨b, u, hu, hfinite⟩ := exists_common_nat_direction (fun j => (p j).map φ) base hreg
  refine ⟨b, u, hu, ?_⟩
  intro j
  apply (hfinite j).subset
  intro x hx k
  rw [system_eval_map]
  exact hx k

end LeanCanny.Geometry.ProjectionCritical
