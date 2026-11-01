/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalSubstitution
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharZero.Infinite
/-! # Exact-degree affine parameter clearing without denominator inverses

The constructed polynomial uses only addition, multiplication and natural
powers in the old coefficient algebra. Division occurs only in its field
interpretation theorem.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedAffinePolynomial
open Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A]

noncomputable def polynomial (D : ℕ) (p : Polynomial A) (a b q : A) : Polynomial A :=
  ∑ k ∈ p.support, C (p.coeff k * q ^ (D-k)) * (C a + C b * X) ^ k

theorem degree_le (D : ℕ) (p : Polynomial A) (a b q : A) : (polynomial D p a b q).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have Hk := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
  have HN : (C a + C b * X : Polynomial A).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le (by simp only [Polynomial.natDegree_C]; omega) (Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, Nat.zero_add] using (Polynomial.natDegree_X_le (R := A)))))
  calc
    _ ≤ (C (p.coeff k * q^(D-k))).natDegree + ((C a + C b * X)^k).natDegree := Polynomial.natDegree_mul_le
    _ = ((C a + C b * X)^k).natDegree := by simp only [Polynomial.natDegree_C, Nat.zero_add]
    _ ≤ k * (C a + C b * X : Polynomial A).natDegree := Polynomial.natDegree_pow_le
    _ ≤ k := by simpa only [mul_one] using Nat.mul_le_mul_left k HN
    _ ≤ p.natDegree := Hk

theorem eval {K : Type*} [Field K] (φ : A →+* K) (D : ℕ) (p : Polynomial A) (a b q : A)
    (hD : p.natDegree ≤ D) (hq : φ q ≠ 0) (t : K) :
    (polynomial D p a b q).eval₂ φ t = φ q ^ D * p.eval₂ φ ((φ a + φ b * t) / φ q) := by
  simp only [polynomial, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_add, eval₂_X, map_mul, map_pow]
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have Hk : k ≤ D := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)).trans hD
  have H := RationalSubstitution.scale_div_pow (φ a + φ b * t) (φ q) D k Hk hq
  calc
    (φ (p.coeff k) * φ q^(D-k)) * (φ a+φ b*t)^k = φ (p.coeff k) * ((φ a+φ b*t)^k * φ q^(D-k)) := by ring
    _ = φ (p.coeff k) * (φ q^D * ((φ a+φ b*t)/φ q)^k) := congrArg (φ (p.coeff k) * ·) H.symm
    _ = φ q^D * (φ (p.coeff k) * ((φ a+φ b*t)/φ q)^k) := by ring

theorem selected_nonzero (φ : A →+* ℝ) (D : ℕ) (p : Polynomial A) (a b q : A)
    (hD : p.natDegree ≤ D) (hp : p.map φ ≠ 0) (hb : φ b ≠ 0) (hq : φ q ≠ 0) :
    (polynomial D p a b q).map φ ≠ 0 := by
  intro HZ
  apply hp
  apply Polynomial.funext
  intro t
  let u := (φ q*t-φ a)/(φ b)
  have HU : (φ a+φ b*u)/φ q = t := by dsimp only [u]; field_simp; ring
  have H := congrArg (fun f : Polynomial ℝ => f.eval u) HZ
  rw [Polynomial.eval_map, eval φ D p a b q hD hq, HU, Polynomial.eval_zero] at H
  simpa only [Polynomial.eval_zero, Polynomial.eval_map] using (mul_eq_zero.mp H).resolve_left (pow_ne_zero D hq)

end LeanCanny.Algebra.ClearedAffinePolynomial
