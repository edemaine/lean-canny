/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Degree bounds in a coefficient-ring parameter -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial
open scoped BigOperators Classical

/-- The coefficient polynomials have parameter degree at most `H`. -/
@[expose] def HasParameterDegree {ι : Type*} (p : MvPolynomial ι (Polynomial ℤ)) (H : ℕ) : Prop :=
  ∀ e, (p.coeff e).natDegree ≤ H

namespace HasParameterDegree

variable {ι : Type*} {p q : MvPolynomial ι (Polynomial ℤ)} {H K : ℕ}

theorem mono (hp : HasParameterDegree p H) (h : H ≤ K) : HasParameterDegree p K :=
  fun e => (hp e).trans h

theorem monomial (e : ι →₀ ℕ) (a : Polynomial ℤ) (ha : a.natDegree ≤ H) :
    HasParameterDegree (MvPolynomial.monomial e a) H := by
  intro f
  simp only [MvPolynomial.coeff_monomial]
  split_ifs
  · exact ha
  · simp

theorem C (a : Polynomial ℤ) (ha : a.natDegree ≤ H) :
    HasParameterDegree (MvPolynomial.C a : MvPolynomial ι (Polynomial ℤ)) H :=
  monomial 0 a ha

theorem X (i : ι) : HasParameterDegree (MvPolynomial.X i : MvPolynomial ι (Polynomial ℤ)) 0 :=
  monomial _ 1 (by simp)

theorem map_C (F : MvPolynomial ι ℤ) : HasParameterDegree (F.map Polynomial.C) 0 := by
  intro e
  rw [MvPolynomial.coeff_map, Polynomial.natDegree_C]

theorem zero : HasParameterDegree (0 : MvPolynomial ι (Polynomial ℤ)) H := by
  intro e
  simp

theorem add (hp : HasParameterDegree p H) (hq : HasParameterDegree q K) :
    HasParameterDegree (p + q) (max H K) := by
  intro e
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (hp e) (hq e))

theorem neg (hp : HasParameterDegree p H) : HasParameterDegree (-p) H := by
  intro e
  simpa only [MvPolynomial.coeff_neg, Polynomial.natDegree_neg] using hp e

theorem sub (hp : HasParameterDegree p H) (hq : HasParameterDegree q K) :
    HasParameterDegree (p - q) (max H K) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem sum {J : Type*} (s : Finset J) (f : J → MvPolynomial ι (Polynomial ℤ))
    (hf : ∀ j ∈ s, HasParameterDegree (f j) H) :
    HasParameterDegree (∑ j ∈ s, f j) H := by
  intro e
  rw [MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact hf j hj e

theorem mul (hp : HasParameterDegree p H) (hq : HasParameterDegree q K) :
    HasParameterDegree (p * q) (H + K) := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, MvPolynomial.monomial_mul_monomial]
  apply sum
  intro e _
  apply sum
  intro f _
  exact monomial _ _ (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp e) (hq f)))

theorem one : HasParameterDegree (1 : MvPolynomial ι (Polynomial ℤ)) 0 := by
  change HasParameterDegree (MvPolynomial.monomial 0 1) 0
  exact monomial _ _ (by simp)

theorem pow (hp : HasParameterDegree p H) (k : ℕ) : HasParameterDegree (p ^ k) (k * H) := by
  induction k with
  | zero => simpa only [pow_zero, Nat.zero_mul] using (one (ι := ι))
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hp

theorem prod {J : Type*} (s : Finset J) (f : J → MvPolynomial ι (Polynomial ℤ))
    (hf : ∀ j ∈ s, HasParameterDegree (f j) H) :
    HasParameterDegree (∏ j ∈ s, f j) (s.card * H) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.card_empty, Nat.zero_mul] using (one (ι := ι))
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, Nat.succ_mul]
    simpa only [Nat.add_comm] using (hf j (Finset.mem_insert_self j s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem pderiv (hp : HasParameterDegree p H) (i : ι) : HasParameterDegree (MvPolynomial.pderiv i p) H := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply sum
  intro e _
  rw [pderiv_monomial]
  apply monomial
  apply Polynomial.natDegree_mul_le.trans
  simpa only [Polynomial.natDegree_natCast, Nat.add_zero] using hp e

/-- Determinants in the small variable-indexed matrix preserve short degree bounds. -/
theorem det {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ (MvPolynomial ι (Polynomial ℤ)))
    (hA : ∀ i j, HasParameterDegree (A i j) H) :
    HasParameterDegree A.det (Fintype.card κ * H) := by
  rw [Matrix.det_apply]
  apply sum
  intro π _
  have hprod := prod Finset.univ (fun j => A (π j) j) (fun j _ => hA (π j) j)
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
  · simpa [hs, Units.smul_def] using hprod
  · simpa [hs, Units.smul_def] using hprod.neg

end HasParameterDegree
end LeanCanny.CountingHierarchy
