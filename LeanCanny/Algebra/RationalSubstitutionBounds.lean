/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitution
public import LeanCanny.Algebra.CoefficientMass
import Mathlib.Tactic.Ring

/-!
# Coefficient budgets for sign-preserving rational substitution

Coordinate numerator and denominator coefficient masses have separate binary
allowances. The cleared numerator's coefficient bit length depends on sums of
these allowances weighted by the original variable degrees, without expanding
the common denominator or storing the resulting polynomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

noncomputable def sourceMass (p : MvPolynomial σ ℤ) : ℕ := ∑ e ∈ p.support, (p.coeff e).natAbs

theorem card_support_le_uniform (p : MvPolynomial σ ℤ) (D : ℕ) (hD : ∀ i, p.degreeOf i ≤ D) :
    p.support.card ≤ (D + 1) ^ Fintype.card σ := by
  classical
  let f : p.support → (σ → Fin (D + 1)) := fun e i =>
    ⟨e.val i, ((MvPolynomial.monomial_le_degreeOf i e.property).trans (hD i)).trans_lt (Nat.lt_succ_self D)⟩
  have hf : Function.Injective f := by
    intro e g he
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun he i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using h

theorem sourceMass_le_pow_uniform (p : MvPolynomial σ ℤ) (D b : ℕ)
    (hD : ∀ i, p.degreeOf i ≤ D) (hb : ∀ e, (p.coeff e).natAbs ≤ 2 ^ b) :
    sourceMass p ≤ 2 ^ (b + Fintype.card σ * (D + 1).size) := by
  classical
  have hm : sourceMass p ≤ p.support.card * 2 ^ b := by
    exact (Finset.sum_le_sum (fun e (_ : e ∈ p.support) => hb e)).trans_eq
      (by simp only [Finset.sum_const, smul_eq_mul])
  calc
    _ ≤ p.support.card * 2 ^ b := hm
    _ ≤ (D + 1) ^ Fintype.card σ * 2 ^ b := Nat.mul_le_mul_right _ (card_support_le_uniform p D hD)
    _ ≤ (2 ^ (D + 1).size) ^ Fintype.card σ * 2 ^ b :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_size_self (D + 1)).le _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

theorem coefficientMass_clearedWith_le (D : σ → ℕ) (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X])
    (hD : ∀ i, p.degreeOf i ≤ D i) (M : σ → ℕ)
    (hn : ∀ i, coefficientMass (n i) ≤ M i) (hd : ∀ i, coefficientMass (d i) ≤ M i) :
    coefficientMass (clearedWith D p n d) ≤ sourceMass p * ∏ i, M i ^ (2 * D i) := by
  classical
  have hfactor (e : σ →₀ ℕ) (he : e ∈ p.support) (i : σ) :
      coefficientMass (n i ^ e i * d i ^ (2 * D i - e i)) ≤ M i ^ (2 * D i) := by
    have hmon : e i ≤ 2 * D i := ((MvPolynomial.monomial_le_degreeOf i he).trans (hD i)).trans (by omega)
    calc
      _ ≤ coefficientMass (n i ^ e i) * coefficientMass (d i ^ (2 * D i - e i)) :=
        coefficientMass_mul_le _ _
      _ ≤ coefficientMass (n i) ^ e i * coefficientMass (d i) ^ (2 * D i - e i) :=
        Nat.mul_le_mul (coefficientMass_pow_le _ _) (coefficientMass_pow_le _ _)
      _ ≤ M i ^ e i * M i ^ (2 * D i - e i) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hn i) _) (Nat.pow_le_pow_left (hd i) _)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hmon]
  unfold clearedWith
  calc
    _ ≤ ∑ e ∈ p.support,
        coefficientMass (C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)) :=
      coefficientMass_sum_le _ _
    _ ≤ ∑ e ∈ p.support, (p.coeff e).natAbs * ∏ i, M i ^ (2 * D i) := by
      apply Finset.sum_le_sum
      intro e he
      apply (coefficientMass_mul_le _ _).trans
      rw [coefficientMass_C]
      apply Nat.mul_le_mul_left
      exact (coefficientMass_prod_le _ _).trans (Finset.prod_le_prod (fun i _ => hfactor e he i))
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem coefficientMass_cleared_le (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (M : σ → ℕ)
    (hn : ∀ i, coefficientMass (n i) ≤ M i) (hd : ∀ i, coefficientMass (d i) ≤ M i) :
    coefficientMass (cleared p n d) ≤ sourceMass p * ∏ i, M i ^ (2 * p.degreeOf i) := by
  exact coefficientMass_clearedWith_le p.degreeOf p n d (fun _ => le_rfl) M hn hd

theorem coefficientMass_cleared_le_pow (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (s : ℕ) (b : σ → ℕ)
    (hp : sourceMass p ≤ 2 ^ s)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ b i) (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ b i) :
    coefficientMass (cleared p n d) ≤ 2 ^ (s + ∑ i, 2 * p.degreeOf i * b i) := by
  classical
  have he : (∏ i, (2 ^ b i) ^ (2 * p.degreeOf i)) = 2 ^ (∑ i, 2 * p.degreeOf i * b i) := by
    calc
      _ = ∏ i, 2 ^ (2 * p.degreeOf i * b i) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← pow_mul, Nat.mul_comm]
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  exact (coefficientMass_cleared_le p n d _ hn hd).trans
    ((Nat.mul_le_mul_right _ hp).trans_eq (by rw [he, ← pow_add]))

theorem coeff_size_cleared_le (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (s : ℕ) (b : σ → ℕ)
    (hp : sourceMass p ≤ 2 ^ s)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ b i) (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ b i) (k : ℕ) :
    ((cleared p n d).coeff k).natAbs.size ≤ s + (∑ i, 2 * p.degreeOf i * b i) + 1 := by
  have h := (coeff_natAbs_le_coefficientMass (cleared p n d) k).trans
    (coefficientMass_cleared_le_pow p n d s b hp hn hd)
  simpa only [Nat.size_pow] using Nat.size_le_size h

theorem coeff_size_cleared_le_uniform (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (s b D : ℕ)
    (hp : sourceMass p ≤ 2 ^ s) (hD : ∀ i, p.degreeOf i ≤ D)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ b) (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ b) (k : ℕ) :
    ((cleared p n d).coeff k).natAbs.size ≤ s + 2 * Fintype.card σ * D * b + 1 := by
  classical
  have h := coeff_size_cleared_le p n d s (fun _ => b) hp hn hd k
  have hs : (∑ i, 2 * p.degreeOf i * b) ≤ 2 * Fintype.card σ * D * b := by
    calc
      _ ≤ ∑ _i : σ, 2 * D * b := Finset.sum_le_sum
        (fun i _ => Nat.mul_le_mul_right b (Nat.mul_le_mul_left 2 (hD i)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
  omega

theorem natDegree_cleared_le_uniform {R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (n d : σ → R[X]) (D E : ℕ)
    (hD : ∀ i, p.degreeOf i ≤ D) (hn : ∀ i, (n i).natDegree ≤ E) (hd : ∀ i, (d i).natDegree ≤ E) :
    (cleared p n d).natDegree ≤ 2 * Fintype.card σ * D * E := by
  classical
  apply (natDegree_cleared_le p n d).trans
  calc
    _ ≤ ∑ _i : σ, 2 * D * E := Finset.sum_le_sum (fun i _ =>
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hD i)) (max_le (hn i) (hd i)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

end LeanCanny.Algebra.RationalSubstitution
