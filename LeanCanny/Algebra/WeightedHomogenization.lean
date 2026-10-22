/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Homogenization in selected variable blocks

Weights zero and one keep coefficient parameters unchanged while homogenizing
point variables. The degree allowance is explicit and need only bound the
weighted degrees of supported monomials. A requested output coefficient is one
original coefficient or zero. High weighted-degree terms are discarded when the
allowance is too small; all evaluation theorems state the required bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.WeightedHomogenization
open MvPolynomial
open scoped BigOperators

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

def weights (w : σ → ℕ) : Option σ → ℕ
  | none => 1
  | some i => w i

theorem weight_split (w : σ → ℕ) (m : Option σ →₀ ℕ) :
    Finsupp.weight (weights w) m = m none + Finsupp.weight w m.some := by
  rw [Finsupp.weight_eq_sum, univ_option, Finset.sum_insertNone, Finsupp.weight_eq_sum]
  simp only [weights, smul_eq_mul, mul_one, Finsupp.some_apply]

theorem degree_split (m : Option σ →₀ ℕ) : m.degree = m none + m.some.degree := by
  rw [Finsupp.degree_eq_sum, univ_option, Finset.sum_insertNone, Finsupp.degree_eq_sum]
  rfl

noncomputable def exponent (w : σ → ℕ) (D : ℕ) (e : σ →₀ ℕ) : Option σ →₀ ℕ :=
  e.optionElim (D - Finsupp.weight w e)

omit [Fintype σ] in
@[simp] theorem exponent_some (w : σ → ℕ) (D : ℕ) (e : σ →₀ ℕ) : (exponent w D e).some = e :=
  Finsupp.some_optionElim _ _

theorem exponent_weight (w : σ → ℕ) (D : ℕ) (e : σ →₀ ℕ) (he : Finsupp.weight w e ≤ D) :
    Finsupp.weight (weights w) (exponent w D e) = D := by
  rw [weight_split, exponent_some]
  simp only [exponent, Finsupp.optionElim_apply_none]
  omega

theorem exponent_eq_iff (w : σ → ℕ) (D : ℕ) (m : Option σ →₀ ℕ)
    (hm : Finsupp.weight (weights w) m = D) (e : σ →₀ ℕ) : exponent w D e = m ↔ e = m.some := by
  constructor
  · intro h
    simpa only [exponent_some] using congrArg Finsupp.some h
  · rintro rfl
    have hh := weight_split w m
    ext i
    cases i with
    | none => simp only [exponent, Finsupp.optionElim_apply_none]; omega
    | some i => simp [exponent]

noncomputable def homogenize (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R) : MvPolynomial (Option σ) R :=
  ∑ e ∈ p.support.filter (fun e => Finsupp.weight w e ≤ D), monomial (exponent w D e) (p.coeff e)

theorem homogeneous (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R) :
    (homogenize w D p).IsWeightedHomogeneous (weights w) D := by
  classical
  apply IsWeightedHomogeneous.sum
  intro e he
  exact isWeightedHomogeneous_monomial _ _ _ (exponent_weight w D e (Finset.mem_filter.mp he).2)

theorem coefficient (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R) (m : Option σ →₀ ℕ) :
    (homogenize w D p).coeff m = if Finsupp.weight (weights w) m = D then p.coeff m.some else 0 := by
  classical
  by_cases hm : Finsupp.weight (weights w) m = D
  · rw [ite_eq_left hm]
    have hs : Finsupp.weight w m.some ≤ D := by have hh := weight_split w m; omega
    simp only [homogenize, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      exponent_eq_iff w D m hm, Finset.sum_ite_eq', Finset.mem_filter, hs, and_true]
    by_cases hp : m.some ∈ p.support
    · simp [hp]
    · simp [hp, MvPolynomial.notMem_support_iff.mp hp]
  · rw [ite_eq_right hm]
    exact (homogeneous w D p).coeff_eq_zero m hm

theorem eval_chart {S : Type*} [CommSemiring S] (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R)
    (hp : ∀ e ∈ p.support, Finsupp.weight w e ≤ D) (φ : R →+* S) (x : σ → S) :
    (homogenize w D p).eval₂ φ (fun i => i.elim 1 x) = p.eval₂ φ x := by
  classical
  have hf : p.support.filter (fun e => Finsupp.weight w e ≤ D) = p.support := Finset.filter_eq_self.mpr hp
  have he (e : σ →₀ ℕ) :
      (exponent w D e).prod (fun i k => (i.elim (1 : S) x) ^ k) = e.prod (fun i k => x i ^ k) := by
    rw [Finsupp.prod_option_index]
    · simp [exponent]
    · intro i; simp
    · intro i a b; exact pow_add _ _ _
  calc
    _ = ∑ e ∈ p.support, φ (p.coeff e) * e.prod (fun i k => x i ^ k) := by
      rw [homogenize, hf, MvPolynomial.eval₂_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [MvPolynomial.eval₂_monomial, he]
    _ = p.eval₂ φ x := by
      conv_rhs => rw [p.as_sum, MvPolynomial.eval₂_sum]
      simp only [MvPolynomial.eval₂_monomial]

theorem map_homogenize {S : Type*} [CommSemiring S] (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R)
    (φ : R →+* S) : (homogenize w D p).map φ = homogenize w D (p.map φ) := by
  ext m
  rw [MvPolynomial.coeff_map, coefficient, coefficient]
  split_ifs <;> simp [MvPolynomial.coeff_map]

theorem totalDegree_le (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R) :
    (homogenize w D p).totalDegree ≤ D + p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hc : (homogenize w D p).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  rw [coefficient] at hc
  split_ifs at hc with hd
  · have hp : m.some ∈ p.support := MvPolynomial.mem_support_iff.mpr hc
    have hb := MvPolynomial.le_totalDegree hp
    change m.some.degree ≤ p.totalDegree at hb
    have hs := weight_split w m
    change m.degree ≤ _
    rw [degree_split]
    omega
  · exact False.elim (hc rfl)

theorem support_coordinate_le (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R)
    (hp : p.totalDegree ≤ D) (m : Option σ →₀ ℕ) (hm : m ∈ (homogenize w D p).support)
    (i : Option σ) : m i ≤ D := by
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [coefficient] at hc
  split_ifs at hc with hd
  · have he := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)).trans hp
    change m.some.degree ≤ D at he
    cases i with
    | none => have hs := weight_split w m; omega
    | some i => exact (Finsupp.le_degree i m.some).trans he
  · exact False.elim (hc rfl)

theorem weight_le_degree (w : σ → ℕ) (hw : ∀ i, w i ≤ 1) (e : σ →₀ ℕ) :
    Finsupp.weight w e ≤ e.degree := by
  rw [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul, mul_one] using Nat.mul_le_mul_left (e i) (hw i)

end LeanCanny.Algebra.WeightedHomogenization
