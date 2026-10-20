/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeExpanded
public import LeanCanny.Algebra.MvCoefficientMass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Integer coefficient mass of active tubes and projection equations

Bounds count every parameter and direction variable after flattening. They
depend only on the source polynomial's mass and degree and the number of
constraints, uniformly over all active sets and projection rows.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation
open MvPolynomial Algebra.MvMass

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem constraint_mass (p : MvPolynomial ι ℤ) (i : Constraint ι) :
    mass (constraintPolynomial p i) ≤ mass p + 4 := by
  have hp : mass (spatial p) ≤ mass p := rename_le _ _
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact (add_le _ _).trans (by simp only [X]; omega)
  · have h := add_le (-spatial p) (MvPolynomial.X (.inr (.inr (.inl true))))
    simp only [neg, X] at h
    exact h.trans (by omega)
  · have h1 := add_le (MvPolynomial.X (.inr (.inl j)) : MvPolynomial (Variable ι) ℤ) 1
    have h2 := sub_le (MvPolynomial.X (.inr (.inl j)) + 1 : MvPolynomial (Variable ι) ℤ) (MvPolynomial.X (.inl false))
    have h3 := add_le (MvPolynomial.X (.inr (.inl j)) + 1 - MvPolynomial.X (.inl false) : MvPolynomial (Variable ι) ℤ)
      (MvPolynomial.X (.inr (.inr (.inr (j, false)))))
    simp only [X, one] at h1 h2 h3
    change mass (_ + _ : MvPolynomial (Variable ι) ℤ) ≤ _
    omega
  · have h1 := sub_le (1 : MvPolynomial (Variable ι) ℤ) (MvPolynomial.X (.inl false))
    have h2 := sub_le (1 - MvPolynomial.X (.inl false) : MvPolynomial (Variable ι) ℤ) (MvPolynomial.X (.inr (.inl j)))
    have h3 := add_le (1 - MvPolynomial.X (.inl false) - MvPolynomial.X (.inr (.inl j)) : MvPolynomial (Variable ι) ℤ)
      (MvPolynomial.X (.inr (.inr (.inr (j, true)))))
    simp only [X, one] at h1 h2 h3
    change mass (_ + _ : MvPolynomial (Variable ι) ℤ) ≤ _
    omega

theorem radius_mass (ι : Type*) [Fintype ι] : mass (radiusPolynomial ι) ≤ Fintype.card (Constraint ι) + 1 := by
  have hs : mass (∑ i : Constraint ι, (MvPolynomial.X (.inr (.inr i)) : MvPolynomial (Variable ι) ℤ) ^ 2) ≤
      Fintype.card (Constraint ι) := by
    apply (sum_le _ _).trans
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => pow_le (MvPolynomial.X (.inr (.inr i)) : MvPolynomial (Variable ι) ℤ) 2)
  have ht := pow_le (MvPolynomial.X (.inl true) : MvPolynomial (Variable ι) ℤ) 2
  have h := sub_le (∑ i : Constraint ι, (MvPolynomial.X (.inr (.inr i)) : MvPolynomial (Variable ι) ℤ) ^ 2)
    (MvPolynomial.X (.inl true) ^ 2)
  simp only [X, one_pow] at ht
  exact h.trans (by omega)

end LeanCanny.Geometry.PolynomialPerturbation

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial Algebra.MvMass Algebra.NestedPolynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def massBound (c H : ℕ) : ℕ := (c + 1) ^ 2 + c * (H + 4) ^ 2 + 1

theorem massBound_le_pow (c H B : ℕ) (hH : H ≤ 2 ^ B) : massBound c H ≤ 2 ^ (2 * B + 2 * c + 8) := by
  have hc : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have hB : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hH' : H + 4 ≤ 2 ^ (B + 3) := by rw [pow_add]; norm_num; omega
  have hr : (c + 1) ^ 2 ≤ 2 ^ (2 * c) := by
    exact (Nat.pow_le_pow_left hc 2).trans_eq (by rw [← pow_mul]; congr 1; omega)
  have ht : c * (H + 4) ^ 2 ≤ 2 ^ (2 * B + c + 6) := by
    apply (Nat.mul_le_mul (show c ≤ 2 ^ c by omega) (Nat.pow_le_pow_left hH' 2)).trans
    rw [← pow_mul, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  let E := 2 * B + 2 * c + 6
  have hr' : (c + 1) ^ 2 ≤ 2 ^ E := hr.trans (Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega))
  have ht' : c * (H + 4) ^ 2 ≤ 2 ^ E := ht.trans (Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega))
  have he : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  calc
    massBound c H ≤ 4 * 2 ^ E := by unfold massBound; omega
    _ = 2 ^ (E + 2) := by rw [pow_add]; ring
    _ = _ := by congr 1

theorem integer_polynomial_mass (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    mass (integerPolynomial p s) ≤ massBound (Fintype.card (PolynomialPerturbation.Constraint ι)) (mass p) := by
  classical
  have hr : mass (flatten (radius ι)) ≤ Fintype.card (PolynomialPerturbation.Constraint ι) + 1 := by
    rw [flatten_radius]
    exact (rename_le _ _).trans (PolynomialPerturbation.radius_mass ι)
  have hc (i : PolynomialPerturbation.Constraint ι) : mass (flatten (constraint p i)) ≤ mass p + 4 := by
    rw [flatten_constraint]
    exact (rename_le _ _).trans (PolynomialPerturbation.constraint_mass p i)
  have hsum : mass (∑ i ∈ s, flatten (constraint p i) ^ 2) ≤
      Fintype.card (PolynomialPerturbation.Constraint ι) * (mass p + 4) ^ 2 := by
    apply (sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => (pow_le _ _).trans (Nat.pow_le_pow_left (hc i) 2))).trans
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (Finset.card_le_univ s)
  have hpow := (pow_le (flatten (radius ι)) 2).trans (Nat.pow_le_pow_left hr 2)
  change mass (flatten (energy p s - C (MvPolynomial.X none))) ≤ _
  simp only [map_sub, flatten_C_X, energy, map_add, map_pow, map_sum]
  have h := sub_le (flatten (radius ι) ^ 2 + ∑ i ∈ s, flatten (constraint p i) ^ 2)
    (MvPolynomial.X (.inr none) : MvPolynomial (IntegerCoordinate ι) ℤ)
  have ha := add_le (flatten (radius ι) ^ 2) (∑ i ∈ s, flatten (constraint p i) ^ 2)
  simp only [X] at h
  unfold massBound
  omega

theorem flattened_projection_mass {σ τ : Type*} (p : MvPolynomial σ (MvPolynomial τ ℤ))
    (base : σ) (j : Algebra.ProjectionEquations.Index base) :
    mass (flatten (Algebra.ProjectionEquations.system p base j)) ≤
      (2 * (flatten p).totalDegree + 1) * mass (flatten p) := by
  cases j with
  | none =>
    rw [Algebra.ProjectionEquations.system, Option.map_none, Algebra.ProjectionFlatten.level]
    apply (rename_le _ _).trans
    exact Nat.le_mul_of_pos_left _ (by omega)
  | some i =>
    rw [Algebra.ProjectionEquations.system, Option.map_some, Algebra.ProjectionFlatten.partial_eq]
    let f : Sum σ τ → Sum (Sum σ σ) τ := Sum.map Sum.inl id
    have hi := (rename_le f (pderiv (.inl i.val) (flatten p))).trans (pderiv_le _ _)
    have hb := (rename_le f (pderiv (.inl base) (flatten p))).trans (pderiv_le _ _)
    have hm := mul_le (MvPolynomial.X (.inl (.inr i.val)) : MvPolynomial (Sum (Sum σ σ) τ) ℤ)
      (rename f (pderiv (.inl base) (flatten p)))
    have hs := sub_le (rename f (pderiv (.inl i.val) (flatten p)))
      (MvPolynomial.X (.inl (.inr i.val)) * rename f (pderiv (.inl base) (flatten p)))
    simp only [X, one_mul] at hm
    exact hs.trans (by nlinarith)

theorem integer_projection_mass (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (j : ProjectionIndex ι) : mass (integerProjection p s j) ≤
      (4 * max p.totalDegree 2 + 1) * massBound (Fintype.card (PolynomialPerturbation.Constraint ι)) (mass p) := by
  apply (flattened_projection_mass (polynomial p s) (base ι) j).trans
  have hd := integer_polynomial_degree p s
  have hm := integer_polynomial_mass p s
  apply Nat.mul_le_mul _ hm
  change 2 * (integerPolynomial p s).totalDegree + 1 ≤ _
  omega

end LeanCanny.Geometry.TubePolynomial
