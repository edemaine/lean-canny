/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicMonomialReduction
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-! # Bounded polynomial divided differences -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

variable {A : Type*} [CommRing A] {n : ℕ}

/-- Monomials admit polynomial divided differences, with their expected
 degree and derivative on the diagonal, over every commutative ring. -/
theorem monomial_divided_differences (x : Fin n → A) (e : Fin n →₀ ℕ) (a : A) :
    ∃ d : Fin n → MvPolynomial (Fin n) A,
      C (eval x (monomial e a)) - monomial e a =
        ∑ i, d i * (C (x i) - X i) ∧
      (∀ i, (d i).totalDegree ≤ e.degree - 1) ∧
      (e.degree = 0 → ∀ i, d i = 0) ∧
      (∀ i, eval x (d i) = eval x (pderiv i (monomial e a))) := by
  generalize he : e.degree = k
  induction k using Nat.strong_induction_on generalizing e a with
  | ind k ih =>
    by_cases he0 : e = 0
    · subst e
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> simp
    · obtain ⟨i, hi⟩ : ∃ i, 1 ≤ e i := by
        by_contra h
        apply he0
        ext i
        have : ¬ 1 ≤ e i := fun hi => h ⟨i, hi⟩
        simpa only [Finsupp.zero_apply] using (by omega : e i = 0)
      let e' := LeanCanny.Algebra.MonicMonomialReduction.residual e i 1
      have hdeg : e'.degree + 1 = e.degree :=
        LeanCanny.Algebra.MonicMonomialReduction.residual_degree e i 1 hi
      have hlt : e'.degree < k := by omega
      obtain ⟨d, hd, hbound, hzero, hdiag⟩ := ih e'.degree hlt e' a rfl
      let q : MvPolynomial (Fin n) A := monomial e' a
      have hq : q * X i = monomial e a := by
        rw [← pow_one (X i), ← monomial_add_single,
          LeanCanny.Algebra.MonicMonomialReduction.residual_add e i 1 hi]
      let D : Fin n → MvPolynomial (Fin n) A := fun j =>
        d j * X i + if j = i then C (eval x q) else 0
      refine ⟨D, ?_, ?_, ?_, ?_⟩
      · have hsum : (∑ j, D j * (C (x j) - X j)) =
            (∑ j, d j * (C (x j) - X j)) * X i +
              C (eval x q) * (C (x i) - X i) := by
          simp only [D, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
          simp only [Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hsum, ← hd, ← hq, map_mul, eval_X, map_mul]
        change C (eval x q) * C (x i) - q * X i = _
        ring
      · intro j
        have hX : (X i : MvPolynomial (Fin n) A).totalDegree ≤ 1 := by
          rw [X]; exact (totalDegree_monomial_le _ _).trans (by simp)
        have hC : (if j = i then C (eval x q) else (0 : MvPolynomial (Fin n) A)).totalDegree = 0 := by
          split_ifs <;> simp
        have hb : (d j * X i).totalDegree ≤ e'.degree := by
          by_cases hz : e'.degree = 0
          · simp [hzero hz j]
          · have hm := totalDegree_mul (d j) (X i)
            have hj := hbound j
            omega
        exact (totalDegree_add _ _).trans (by rw [hC]; omega)
      · intro hz
        omega
      · intro j
        rw [← hq, pderiv_mul]
        simp only [D, map_add, map_mul, eval_X, hdiag]
        by_cases hj : j = i
        · subst j
          simp [q]
        · simp [q, hj, Ne.symm hj]

/-- Every polynomial of degree at most `d + 1` has divided differences of
 degree at most `d`, including over rings with zero divisors. -/
theorem polynomial_divided_differences (x : Fin n → A)
    (p : MvPolynomial (Fin n) A) (d : ℕ) (hp : p.totalDegree ≤ d + 1) :
    ∃ D : Fin n → MvPolynomial (Fin n) A,
      C (eval x p) - p = ∑ i, D i * (C (x i) - X i) ∧
      (∀ i, (D i).totalDegree ≤ d) ∧
      (∀ i, eval x (D i) = eval x (pderiv i p)) := by
  choose D hdiff hdeg _ hdiag using
    (fun e : Fin n →₀ ℕ => monomial_divided_differences x e (p.coeff e))
  refine ⟨fun i => ∑ e ∈ p.support, D e i, ?_, ?_, ?_⟩
  · calc
      C (eval x p) - p =
          ∑ e ∈ p.support, (C (eval x (monomial e (p.coeff e))) -
            monomial e (p.coeff e)) := by
        conv_lhs => rw [p.as_sum]
        simp only [map_sum, Finset.sum_sub_distrib]
      _ = ∑ i, (∑ e ∈ p.support, D e i) * (C (x i) - X i) := by
        simp_rw [hdiff]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
  · intro i
    apply totalDegree_finsetSum_le
    intro e he
    have hb : e.degree ≤ p.totalDegree := le_totalDegree he
    exact (hdeg e i).trans (by omega)
  · intro i
    rw [map_sum]
    simp_rw [hdiag]
    conv_rhs => rw [p.as_sum]
    simp only [map_sum]

end LeanCanny.CountingHierarchy
