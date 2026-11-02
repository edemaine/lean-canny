/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.TrailingCoefficientMap
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Recovering original coordinates before infinitesimal extraction

`p` has outer coordinate variable T and inner dilation variable E. Replacing
T by E*T precedes taking the lowest E coefficient. The resulting reader is an
index shift, without a division or an inverse in the retained coefficient ring.
-/
@[expose] public section
namespace LeanCanny.Algebra.DilatedCoordinatePolynomial
open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def rescale (p : Polynomial (Polynomial R)) : Polynomial (Polynomial R) :=
  p.comp (C X * X)

theorem coefficient (p : Polynomial (Polynomial R)) (c k : ℕ) :
    ((rescale p).coeff k).coeff c = if k ≤ c then (p.coeff k).coeff (c-k) else 0 := by
  rw [rescale,comp_C_mul_X_coeff,coeff_mul_X_pow']

theorem coefficient_shift (p : Polynomial (Polynomial R)) (c k : ℕ) :
    ((rescale p).coeff k).coeff (c+k) = (p.coeff k).coeff c := by
  rw [rescale,comp_C_mul_X_coeff,coeff_mul_X_pow]

theorem eval_rescale {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Polynomial (Polynomial R)) (e x : S) :
    eval₂ (eval₂RingHom φ e) x (rescale p) = eval₂ (eval₂RingHom φ e) (e*x) p := by
  simp [rescale,eval₂_comp]

theorem root (p : Polynomial (Polynomial R)) (e x : R)
    (h : eval₂ (evalRingHom e) (e*x) p = 0) :
    eval₂ (evalRingHom e) x (rescale p) = 0 := by
  have H := eval_rescale (RingHom.id R) p e x
  change eval₂ (evalRingHom e) x (rescale p) = eval₂ (evalRingHom e) (e*x) p at H
  exact H.trans h

theorem swap_coefficient (p : Polynomial (Polynomial R)) (c k : ℕ) :
    ((Bivariate.swap p).coeff c).coeff k = (p.coeff k).coeff c := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,coeff_add,hp,hq]
  | monomial n a =>
      simp only [Bivariate.swap_monomial,coeff_mul_C,coeff_map,coeff_C_mul,coeff_X_pow,
        coeff_monomial]
      split_ifs <;> simp_all

theorem swapped_coefficient (p : Polynomial (Polynomial R)) (c k : ℕ) :
    ((Bivariate.swap (rescale p)).coeff c).coeff k =
      if k ≤ c then (p.coeff k).coeff (c-k) else 0 := by
  rw [swap_coefficient,coefficient]

/-- A monic original coordinate equation supplies a nonzero E coefficient at
its original coordinate degree; no new search bound depends on a norm degree. -/
theorem trailing_degree_le [Nontrivial R] (p : Polynomial (Polynomial R)) (d : ℕ)
    (hd : p.coeff d = 1) : (Bivariate.swap (rescale p)).natTrailingDegree ≤ d := by
  apply natTrailingDegree_le_of_ne_zero
  intro hz
  have H := congrArg (fun q : Polynomial R => q.coeff d) hz
  rw [swapped_coefficient,ite_eq_left (Nat.le_refl d),Nat.sub_self,hd,coeff_one,coeff_zero] at H
  exact one_ne_zero H

theorem trailing_degree_le_of_constant (p : Polynomial (Polynomial R)) (d : ℕ)
    (a : R) (ha : a ≠ 0) (hd : p.coeff d = C a) :
    (Bivariate.swap (rescale p)).natTrailingDegree ≤ d := by
  apply natTrailingDegree_le_of_ne_zero
  intro hz
  have H := congrArg (fun q : Polynomial R => q.coeff d) hz
  rw [swapped_coefficient,ite_eq_left (Nat.le_refl d),Nat.sub_self,hd,coeff_C_zero,coeff_zero] at H
  exact ha H

theorem coefficient_degree (p : Polynomial (Polynomial R)) (c : ℕ) :
    ((Bivariate.swap (rescale p)).coeff c).natDegree ≤ c := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [swapped_coefficient,ite_eq_right (by omega : ¬k ≤ c)]

theorem trailing_coordinate_degree (p : Polynomial (Polynomial R)) (d : ℕ)
    (a : R) (ha : a ≠ 0) (hd : p.coeff d = C a) :
    (Bivariate.swap (rescale p)).trailingCoeff.natDegree ≤ d := by
  exact (coefficient_degree p _).trans (trailing_degree_le_of_constant p d a ha hd)

end LeanCanny.Algebra.DilatedCoordinatePolynomial
