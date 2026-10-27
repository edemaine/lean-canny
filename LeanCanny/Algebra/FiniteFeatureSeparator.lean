/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Algebra.Field.ZMod

/-! # One-parameter separators for finite feature vectors

Over a sufficiently large finite field, powers of one field element give a
linear functional separating any finite family of distinct vectors. The
exceptional parameter polynomial has degree at most the number of features
times the square of the family size. No table of independent weights is
needed. This is an existence theorem; selecting the parameter still requires
a native test of separation in each application.
-/

@[expose] public section
namespace LeanCanny.Algebra.FiniteFeatureSeparator
open Polynomial
open scoped Classical BigOperators

variable {K τ : Type*} [Field K] [Fintype τ] {n : ℕ}

noncomputable def vectorPolynomial (v : Fin n → K) : K[X] :=
  ∑ i, monomial i.val (v i)

theorem coefficient (v : Fin n → K) (i : Fin n) : (vectorPolynomial v).coeff i.val = v i := by
  simp only [vectorPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact ite_eq_right (fun h => hji (Fin.ext h))
  · simp

theorem vectorPolynomial_injective : Function.Injective (vectorPolynomial (K := K) (n := n)) := by
  intro v w h
  funext i
  have he := congrArg (fun p : K[X] => p.coeff i.val) h
  simpa only [coefficient] using he

theorem degree_le (v : Fin n → K) : (vectorPolynomial v).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans i.isLt.le

theorem eval_eq (v : Fin n → K) (t : K) : (vectorPolynomial v).eval t = ∑ i, v i * t ^ i.val := by
  simp only [vectorPolynomial, eval_finsetSum, eval_monomial]

noncomputable def collision (a : τ → Fin n → K) (j : τ × τ) : K[X] :=
  if j.1 = j.2 then 1 else vectorPolynomial (a j.1) - vectorPolynomial (a j.2)

omit [Fintype τ] in
theorem collision_nonzero (a : τ → Fin n → K) (ha : Function.Injective a) (j : τ × τ) :
    collision a j ≠ 0 := by
  by_cases he : j.1 = j.2
  · simp only [collision, he, ite_true, ne_eq, one_ne_zero, not_false_eq_true]
  · rw [collision, ite_eq_right he, sub_ne_zero]
    exact fun h => he (ha (vectorPolynomial_injective h))

omit [Fintype τ] in
theorem collision_degree (a : τ → Fin n → K) (j : τ × τ) : (collision a j).natDegree ≤ n := by
  by_cases he : j.1 = j.2
  · simp only [collision, he, ite_true, natDegree_one, Nat.zero_le]
  · rw [collision, ite_eq_right he]
    exact (natDegree_sub_le _ _).trans (max_le (degree_le _) (degree_le _))

theorem exists_parameter [Fintype K] (a : τ → Fin n → K) (ha : Function.Injective a)
    (hcard : n * Fintype.card τ ^ 2 < Fintype.card K) :
    ∃ t : K, Function.Injective (fun x => ∑ i, a x i * t ^ i.val) := by
  let H := ∏ j : τ × τ, collision a j
  have hn : H ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => collision_nonzero a ha j)
  have hd : H.natDegree ≤ n * Fintype.card τ ^ 2 := by
    apply (natDegree_prod_le _ _).trans
    calc
      ∑ j : τ × τ, (collision a j).natDegree ≤ ∑ _j : τ × τ, n :=
        Finset.sum_le_sum (fun j _ => collision_degree a j)
      _ = n * Fintype.card τ ^ 2 := by simp [Fintype.card_prod, pow_two, Nat.mul_comm]
  have hex : ∃ t : K, H.eval t ≠ 0 := by
    by_contra he
    apply hn
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero H Function.injective_id
    · intro t
      by_contra ht
      exact he ⟨t, ht⟩
    · exact hd.trans_lt hcard
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ?_⟩
  intro x y he
  by_contra hxy
  have hc := Finset.prod_ne_zero_iff.mp (show (∏ j : τ × τ, (collision a j).eval t) ≠ 0 by
    simpa only [H, eval_prod] using ht) (x, y) (Finset.mem_univ _)
  apply hc
  simp only [collision, hxy, ite_false, eval_sub, eval_eq]
  exact sub_eq_zero.mpr he

theorem exists_prime_parameter (a : τ → Fin n → ℤ) (ha : Function.Injective a)
    (hb : ∀ x i, -1 ≤ a x i ∧ a x i ≤ 1) :
    ∃ p : ℕ, p.Prime ∧ n * Fintype.card τ ^ 2 + 2 < p ∧
      p ≤ 2 * (n * Fintype.card τ ^ 2 + 2) ∧
      ∃ t : ZMod p, Function.Injective (fun x => ∑ i, (a x i : ZMod p) * t ^ i.val) := by
  obtain ⟨p, hp, hl, hu⟩ := Nat.exists_prime_lt_and_le_two_mul (n * Fintype.card τ ^ 2 + 2) (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hcast {u v : ℤ} (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1)
      (he : (u : ZMod p) = (v : ZMod p)) : u = v := by
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub u v p).mp he
    have hs : (v - u).natAbs < (p : ℤ).natAbs := by
      rw [Int.natAbs_natCast]
      omega
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hs
    omega
  have hi : Function.Injective (fun x i => (a x i : ZMod p)) := by
    intro x y he
    apply ha
    funext i
    exact hcast (hb x i) (hb y i) (congrFun he i)
  refine ⟨p, hp, hl, hu, ?_⟩
  apply exists_parameter (fun x i => (a x i : ZMod p)) hi
  rw [ZMod.card]
  omega

end LeanCanny.Algebra.FiniteFeatureSeparator
