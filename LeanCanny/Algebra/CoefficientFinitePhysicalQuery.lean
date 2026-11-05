/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialDyadicInterpolation
public import Mathlib.Algebra.MvPolynomial.Variables
/-! # Exact finite physical-variable representatives, with coefficient bounds -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientFinitePhysicalQuery
open Polynomial MvPolynomial
open scoped Classical

variable {R : Type*} [CommSemiring R]

noncomputable def polynomial (N : ℕ) (q : MvPolynomial ℕ R) (h : ∀ i ∈ q.vars, i < N) :
    MvPolynomial (Fin N) R := Classical.choose
  (MvPolynomial.exists_rename_eq_of_vars_subset_range q Fin.val Fin.val_injective
    (fun i hi => ⟨⟨i, h i hi⟩, rfl⟩))

theorem rename_polynomial (N : ℕ) (q : MvPolynomial ℕ R) (h : ∀ i ∈ q.vars, i < N) :
    MvPolynomial.rename Fin.val (polynomial N q h) = q := by
  unfold polynomial
  exact Classical.choose_spec (MvPolynomial.exists_rename_eq_of_vars_subset_range q Fin.val Fin.val_injective
    (fun i hi => ⟨⟨i, h i hi⟩, rfl⟩))

theorem coefficient (N : ℕ) (q : MvPolynomial ℕ R) (h : ∀ i ∈ q.vars, i < N) (e : Fin N →₀ ℕ) :
    (polynomial N q h).coeff e = q.coeff (e.mapDomain Fin.val) := by
  conv_rhs => rw [← rename_polynomial N q h]
  rw [MvPolynomial.coeff_rename_mapDomain Fin.val Fin.val_injective]

theorem degree_eq (N : ℕ) (q : MvPolynomial ℕ R) (h : ∀ i ∈ q.vars, i < N) :
    (polynomial N q h).totalDegree = q.totalDegree := by
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    have hq : e.mapDomain Fin.val ∈ q.support := by
      rw [MvPolynomial.mem_support_iff, ← coefficient N q h e]
      exact MvPolynomial.mem_support_iff.mp he
    have hs : (e.mapDomain Fin.val).sum (fun _ k => k) = e.sum (fun _ k => k) :=
      Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    rw [← hs]
    exact MvPolynomial.le_totalDegree hq
  · calc
      q.totalDegree = (MvPolynomial.rename Fin.val (polynomial N q h)).totalDegree :=
        congrArg MvPolynomial.totalDegree (rename_polynomial N q h).symm
      _ ≤ (polynomial N q h).totalDegree := MvPolynomial.totalDegree_rename_le _ _

noncomputable def natural {A : Type*} [Zero A] {N : ℕ} (z : Fin N → A) (i : ℕ) : A :=
  if hi : i < N then z ⟨i, hi⟩ else 0

theorem evaluation {A : Type*} [CommSemiring A] (φ : R →+* A) (N : ℕ)
    (q : MvPolynomial ℕ R) (h : ∀ i ∈ q.vars, i < N) (z : Fin N → A) :
    (polynomial N q h).eval₂ φ z = q.eval₂ φ (natural z) := by
  conv_rhs => rw [← rename_polynomial N q h, MvPolynomial.eval₂_rename]
  have hh : natural z ∘ Fin.val = z := by
    funext i
    exact dite_eq_left i.isLt
  rw [hh]

theorem coefficient_degree_mass (N : ℕ) (q : MvPolynomial ℕ ℤ[X]) (h : ∀ i ∈ q.vars, i < N)
    (D H : ℕ) (hb : ∀ e, (q.coeff e).natDegree ≤ D ∧ coefficientMass (q.coeff e) ≤ 2 ^ H)
    (e : Fin N →₀ ℕ) :
    ((polynomial N q h).coeff e).natDegree ≤ D ∧ coefficientMass ((polynomial N q h).coeff e) ≤ 2 ^ H := by
  rw [coefficient]
  exact hb _

end LeanCanny.Algebra.CoefficientFinitePhysicalQuery
