/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationAdditive
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Parameter total-degree bounds for nested multivariate polynomials

Uniform degree bounds on parameter coefficients are closed under sums,
products, spatial differentiation, homogenization, and variable permutations.
In particular, a determinant of size r with coefficient degree at most E has
coefficient degree at most rE.
-/

@[expose] public section
namespace LeanCanny.Algebra.NestedTotalDegree
open MvPolynomial
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

variable {σ τ R : Type*} [CommRing R]

def Bound (p : MvPolynomial σ (MvPolynomial τ R)) (D : ℕ) : Prop :=
  ∀ e, (p.coeff e).totalDegree ≤ D

theorem zero (D : ℕ) : Bound (0 : MvPolynomial σ (MvPolynomial τ R)) D := by
  intro e
  simp

theorem one : Bound (1 : MvPolynomial σ (MvPolynomial τ R)) 0 := by
  intro e
  simp only [coeff_one]
  split_ifs <;> simp

theorem add {p q : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ} (hp : Bound p D) (hq : Bound q D) :
    Bound (p + q) D := by
  intro e
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (totalDegree_add _ _).trans (max_le (hp e) (hq e))

theorem sub {p q : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ} (hp : Bound p D) (hq : Bound q D) :
    Bound (p - q) D := by
  intro e
  rw [coeff_sub]
  exact (totalDegree_sub _ _).trans (max_le (hp e) (hq e))

theorem neg {p : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ} (hp : Bound p D) : Bound (-p) D := by
  intro e
  simpa only [coeff_neg, totalDegree_neg] using hp e

theorem mul {p q : MvPolynomial σ (MvPolynomial τ R)} {D E : ℕ} (hp : Bound p D) (hq : Bound q E) :
    Bound (p * q) (D + E) := by
  intro e
  rw [coeff_mul]
  apply totalDegree_finsetSum_le
  intro a _
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hp a.1) (hq a.2))

theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ (MvPolynomial τ R)) (D : ℕ)
    (hp : ∀ i ∈ s, Bound (p i) D) : Bound (∑ i ∈ s, p i) D := by
  intro e
  rw [MvPolynomial.coeff_sum]
  apply totalDegree_finsetSum_le
  intro i hi
  exact hp i hi e

theorem prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ (MvPolynomial τ R)) (D : ι → ℕ)
    (hp : ∀ i ∈ s, Bound (p i) (D i)) : Bound (∏ i ∈ s, p i) (∑ i ∈ s, D i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul (hp i (Finset.mem_insert_self _ _)) (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem unit_smul {p : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ} (u : ℤˣ) (hp : Bound p D) :
    Bound (u • p) D := by
  rcases Int.units_eq_one_or u with h | h
  · simpa only [h, Units.smul_def, Units.val_one, one_smul] using hp
  · simpa [h, Units.smul_def] using neg hp

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ (MvPolynomial τ R))) (E : ℕ)
    (hA : ∀ i j, Bound (A i j) E) : Bound A.det (Fintype.card ι * E) := by
  rw [Matrix.det_apply]
  apply sum
  intro π _
  apply unit_smul
  have hp := prod Finset.univ (fun j => A (π j) j) (fun _ => E) (fun j _ => hA (π j) j)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using hp

theorem pderiv {p : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ} (hp : Bound p D) (i : σ) :
    Bound (MvPolynomial.pderiv i p) D := by
  intro e
  rw [coeff_pderiv]
  have hnat : (e i : MvPolynomial τ R) + 1 = C ((e i + 1 : ℕ) : R) := by simp
  rw [hnat]
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, Nat.add_zero] using hp _)

theorem homogenize [Fintype σ] {p : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ}
    (hp : Bound p D) (w : σ → ℕ) (B : ℕ) : Bound (WeightedHomogenization.homogenize w B p) D := by
  intro e
  rw [WeightedHomogenization.coefficient]
  split_ifs
  · exact hp _
  · simp

theorem rename {σ' : Type*} (f : σ ≃ σ') {p : MvPolynomial σ (MvPolynomial τ R)} {D : ℕ}
    (hp : Bound p D) : Bound (MvPolynomial.rename f p) D := by
  intro e
  have he : (e.mapDomain f.symm).mapDomain f = e := by
    rw [← Finsupp.mapDomain_comp]
    have hf : (f : σ → σ') ∘ f.symm = id := by funext i; simp
    rw [hf, Finsupp.mapDomain_id]
  rw [← he, coeff_rename_mapDomain f f.injective]
  exact hp _

end LeanCanny.Algebra.NestedTotalDegree
