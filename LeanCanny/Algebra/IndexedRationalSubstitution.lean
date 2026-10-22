/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionMap
public import LeanCanny.Algebra.RationalSubstitutionFactors
import Mathlib.Tactic.Ring

/-!
# Rational substitution from an indexed source term family

An input polynomial is a sum of indexed monomials. The reference representation
allows repeated exponent vectors and zero coefficients. Clearing fixed even
denominator powers is linear in this representation, and evaluation gives the
same sign at every point with nonzero coordinate denominators. The term family
is a specification for streamed access, not a stored exponent array.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.Indexed
open Polynomial
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

noncomputable def exponentVector (A : ℕ) (e : ℕ → ℕ) : Fin A →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e i.val)

noncomputable def source (A M : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ) : MvPolynomial (Fin A) R :=
  ∑ r ∈ Finset.range M, MvPolynomial.monomial (exponentVector A (e r)) (a r)

noncomputable def cleared (A M W : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → R[X]) : R[X] :=
  ∑ r ∈ Finset.range M, C (a r) * ∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)

theorem map_cleared {S : Type*} [CommSemiring S] (φ : R →+* S) (A M W : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → R[X]) :
    (cleared A M W a e n d).map φ =
      cleared A M W (fun r => φ (a r)) e (fun i => (n i).map φ) (fun i => (d i).map φ) := by
  classical
  simp only [cleared, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_C]

theorem eval₂_source {K : Type*} [CommSemiring K] (φ : R →+* K) (A M : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (v : ℕ → K) :
    (source A M a e).eval₂ φ (fun i => v i.val) =
      ∑ r ∈ Finset.range M, φ (a r) * ∏ i ∈ Finset.range A, v i ^ e r i := by
  classical
  simp only [source, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial, Finsupp.prod_pow,
    exponentVector, Finsupp.coe_equivFunOnFinite_symm]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  exact Fin.prod_univ_eq_prod_range (fun i => v i ^ e r i) A

noncomputable def clearHom {σ : Type*} [Fintype σ] (D : σ → ℕ) (n d : σ → R[X]) :
    MvPolynomial σ R →+ R[X] where
  toFun := fun p => RationalSubstitution.clearedWith D p n d
  map_zero' := by simp [RationalSubstitution.clearedWith]
  map_add' := by
    classical
    intro p q
    change Finsupp.sum (AddMonoidAlgebra.coeff (p + q)) (fun e a => C a * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)) =
      Finsupp.sum (AddMonoidAlgebra.coeff p) (fun e a => C a * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)) +
      Finsupp.sum (AddMonoidAlgebra.coeff q) (fun e a => C a * ∏ i, n i ^ e i * d i ^ (2 * D i - e i))
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index (fun _ _ => by simp) (fun _ _ _ _ => by simp only [map_add, add_mul])

theorem clearHom_monomial {σ : Type*} [Fintype σ] (D : σ → ℕ) (n d : σ → R[X]) (e : σ →₀ ℕ) (a : R) :
    clearHom D n d (MvPolynomial.monomial e a) = C a * ∏ i, n i ^ e i * d i ^ (2 * D i - e i) := by
  change Finsupp.sum (Finsupp.single e a) (fun e a => C a * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)) = _
  exact Finsupp.sum_single_index (by simp)

theorem cleared_eq_clearedWith_source (A M D : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → R[X]) :
    cleared A M (2 * D) a e n d = RationalSubstitution.clearedWith (fun _ => D) (source A M a e)
      (fun i => n i.val) (fun i => d i.val) := by
  classical
  symm
  change clearHom (fun _ => D) (fun i : Fin A => n i.val) (fun i => d i.val) (source A M a e) = _
  rw [source, map_sum]
  simp only [clearHom_monomial, exponentVector, Finsupp.coe_equivFunOnFinite_symm, cleared]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  exact Fin.prod_univ_eq_prod_range (fun i => n i ^ e r i * d i ^ (2 * D - e r i)) A

theorem eval₂_cleared {K : Type*} [Field K] (φ : R →+* K) (x : K) (A M W : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → R[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W) (hd : ∀ i, i < A → (d i).eval₂ φ x ≠ 0) :
    (cleared A M W a e n d).eval₂ φ x = (∏ i ∈ Finset.range A, (d i).eval₂ φ x ^ W) *
      (source A M a e).eval₂ φ (fun i => (n i.val).eval₂ φ x / (d i.val).eval₂ φ x) := by
  classical
  let ψ := Polynomial.eval₂RingHom φ x
  have hC (a : R) : ψ (C a) = φ a := Polynomial.eval₂_C _ _
  change ψ (cleared A M W a e n d) = (∏ i ∈ Finset.range A, ψ (d i) ^ W) *
    (source A M a e).eval₂ φ (fun i => ψ (n i.val) / ψ (d i.val))
  simp only [cleared, map_sum, map_mul, map_prod, map_pow, hC]
  rw [eval₂_source φ A M a e (fun i => ψ (n i) / ψ (d i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = φ (a r) * ∏ i ∈ Finset.range A, ψ (d i) ^ W * (ψ (n i) / ψ (d i)) ^ e r i := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (RationalSubstitution.scale_div_pow _ _ _ _
        (he r (Finset.mem_range.mp hr) i (Finset.mem_range.mp hi)) (hd i (Finset.mem_range.mp hi))).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem sign_eval₂_cleared (φ : R →+* ℝ) (x : ℝ) (A M D : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → R[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ 2 * D) (hd : ∀ i, i < A → (d i).eval₂ φ x ≠ 0) :
    SignType.sign ((cleared A M (2 * D) a e n d).eval₂ φ x) =
      SignType.sign ((source A M a e).eval₂ φ (fun i => (n i.val).eval₂ φ x / (d i.val).eval₂ φ x)) := by
  have hpos : 0 < ∏ i ∈ Finset.range A, (d i).eval₂ φ x ^ (2 * D) := by
    apply Finset.prod_pos
    intro i hi
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (hd i (Finset.mem_range.mp hi))) _
  rw [eval₂_cleared φ x A M (2 * D) a e n d he hd, sign_mul, sign_pos hpos, one_mul]

end LeanCanny.Algebra.RationalSubstitution.Indexed
