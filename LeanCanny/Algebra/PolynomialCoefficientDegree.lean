/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationAdditive
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.BigOperators

/-! # Sweep-parameter degree bounds for polynomial systems

Spatial differentiation and homogenization preserve a uniform bound on the
degrees of the polynomial coefficients. Products and determinants accumulate
these bounds additively.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialCoefficientDegree
open MvPolynomial
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

variable {σ R : Type*} [CommRing R]

def Bound (p : MvPolynomial σ (Polynomial R)) (D : ℕ) : Prop :=
  ∀ e, (p.coeff e).natDegree ≤ D

theorem mono {p : MvPolynomial σ (Polynomial R)} {D E : ℕ} (hp : Bound p D) (hDE : D ≤ E) :
    Bound p E := fun e => (hp e).trans hDE

theorem zero (D : ℕ) : Bound (0 : MvPolynomial σ (Polynomial R)) D := by intro e; simp

theorem one : Bound (1 : MvPolynomial σ (Polynomial R)) 0 := by
  intro e
  rw [coeff_one]
  split_ifs <;> simp

theorem C {r : Polynomial R} {D : ℕ} (hr : r.natDegree ≤ D) :
    Bound (MvPolynomial.C r : MvPolynomial σ (Polynomial R)) D := by
  intro e
  rw [coeff_C]
  split_ifs
  · exact hr
  · simp

theorem X (i : σ) : Bound (MvPolynomial.X i : MvPolynomial σ (Polynomial R)) 0 := by
  intro e
  rw [coeff_X]
  split_ifs <;> simp

theorem add {p q : MvPolynomial σ (Polynomial R)} {D : ℕ} (hp : Bound p D) (hq : Bound q D) :
    Bound (p + q) D := by
  intro e
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hp e) (hq e))

theorem sub {p q : MvPolynomial σ (Polynomial R)} {D : ℕ} (hp : Bound p D) (hq : Bound q D) :
    Bound (p - q) D := by
  intro e
  rw [coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp e) (hq e))

theorem neg {p : MvPolynomial σ (Polynomial R)} {D : ℕ} (hp : Bound p D) : Bound (-p) D := by
  intro e
  simpa only [coeff_neg, Polynomial.natDegree_neg] using hp e

theorem mul {p q : MvPolynomial σ (Polynomial R)} {D E : ℕ} (hp : Bound p D) (hq : Bound q E) :
    Bound (p * q) (D + E) := by
  intro e
  rw [coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp a.1) (hq a.2))

theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ (Polynomial R)) (D : ℕ)
    (hp : ∀ i ∈ s, Bound (p i) D) : Bound (∑ i ∈ s, p i) D := by
  intro e
  rw [MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact hp i hi e

theorem prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ (Polynomial R)) (D : ι → ℕ)
    (hp : ∀ i ∈ s, Bound (p i) (D i)) : Bound (∏ i ∈ s, p i) (∑ i ∈ s, D i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul (hp i (Finset.mem_insert_self _ _)) (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem pow {p : MvPolynomial σ (Polynomial R)} {D : ℕ} (hp : Bound p D) (N : ℕ) :
    Bound (p ^ N) (N * D) := by
  induction N with
  | zero => simpa only [pow_zero, Nat.zero_mul] using one
  | succ N ih => simpa only [pow_succ, Nat.succ_mul] using mul ih hp

theorem unit_smul {p : MvPolynomial σ (Polynomial R)} {D : ℕ} (u : ℤˣ) (hp : Bound p D) :
    Bound (u • p) D := by
  rcases Int.units_eq_one_or u with h | h
  · simpa only [h, Units.smul_def, Units.val_one, one_smul] using hp
  · simpa [h, Units.smul_def] using neg hp

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ (Polynomial R))) (E : ℕ)
    (hA : ∀ i j, Bound (A i j) E) : Bound A.det (Fintype.card ι * E) := by
  rw [Matrix.det_apply]
  apply sum
  intro π _
  apply unit_smul
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    prod Finset.univ (fun j => A (π j) j) (fun _ => E) (fun j _ => hA (π j) j)

theorem pderiv {p : MvPolynomial σ (Polynomial R)} {D : ℕ} (hp : Bound p D) (i : σ) :
    Bound (MvPolynomial.pderiv i p) D := by
  intro e
  rw [coeff_pderiv]
  have hn : (e i : Polynomial R) + 1 = Polynomial.C ((e i + 1 : ℕ) : R) := by simp
  rw [hn]
  exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, Nat.add_zero] using hp _)

theorem homogenize [Fintype σ] {p : MvPolynomial σ (Polynomial R)} {D : ℕ}
    (hp : Bound p D) (w : σ → ℕ) (B : ℕ) : Bound (WeightedHomogenization.homogenize w B p) D := by
  intro e
  rw [WeightedHomogenization.coefficient]
  split_ifs
  · exact hp _
  · simp

theorem rename {σ' : Type*} (f : σ ≃ σ') {p : MvPolynomial σ (Polynomial R)} {D : ℕ}
    (hp : Bound p D) : Bound (MvPolynomial.rename f p) D := by
  intro e
  have he : (e.mapDomain f.symm).mapDomain f = e := by
    rw [← Finsupp.mapDomain_comp]
    have hf : (f : σ → σ') ∘ f.symm = id := by funext i; simp
    rw [hf, Finsupp.mapDomain_id]
  rw [← he, coeff_rename_mapDomain f f.injective]
  exact hp _

end LeanCanny.Algebra.PolynomialCoefficientDegree
