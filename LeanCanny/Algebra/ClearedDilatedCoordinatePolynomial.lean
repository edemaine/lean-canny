/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.DilatedCoordinatePolynomial
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Dilation with the actual common denominator cleared

The physical dilation parameter can be E/Q. Scaling the roots by Q before
substituting E*T gives a division-free equation for the original coordinate.
Its coefficient reader uses the original coefficient, an index shift, and a
power of Q; no inverse modulo the query modulus is needed.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedDilatedCoordinatePolynomial
open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def rescale (p : Polynomial (Polynomial R)) (q : R) :
    Polynomial (Polynomial R) :=
  DilatedCoordinatePolynomial.rescale (p.scaleRoots (C q))

theorem coefficient (p : Polynomial (Polynomial R)) (q : R) (c k : ℕ) :
    ((rescale p q).coeff k).coeff c =
      if k ≤ c then (p.coeff k).coeff (c-k) * q ^ (p.natDegree-k) else 0 := by
  rw [rescale, DilatedCoordinatePolynomial.coefficient]
  split_ifs with h
  · rw [coeff_scaleRoots, ← map_pow, coeff_mul_C]
  · rfl

theorem swapped_coefficient (p : Polynomial (Polynomial R)) (q : R) (c k : ℕ) :
    ((Bivariate.swap (rescale p q)).coeff c).coeff k =
      if k ≤ c then (p.coeff k).coeff (c-k) * q ^ (p.natDegree-k) else 0 := by
  rw [DilatedCoordinatePolynomial.swap_coefficient, coefficient]

theorem eval_rescale {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Polynomial (Polynomial R)) (q : R) (e y x : S)
    (hy : φ q * y = e * x) :
    eval₂ (eval₂RingHom φ e) x (rescale p q) =
      φ q ^ p.natDegree * eval₂ (eval₂RingHom φ e) y p := by
  rw [rescale, DilatedCoordinatePolynomial.eval_rescale, ← hy]
  have hc : (eval₂RingHom φ e) (C q) = φ q := by
    change eval₂ φ e (C q) = φ q
    rw [eval₂_C]
  simpa only [hc] using
    (scaleRoots_eval₂_mul (p := p) (eval₂RingHom φ e) y (C q))

theorem root {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Polynomial (Polynomial R)) (q : R) (e y x : S)
    (hy : φ q * y = e * x) (hp : eval₂ (eval₂RingHom φ e) y p = 0) :
    eval₂ (eval₂RingHom φ e) x (rescale p q) = 0 := by
  rw [eval_rescale φ p q e y x hy, hp, mul_zero]

theorem trailing_degree_le (p : Polynomial (Polynomial R)) (q a : R)
    (ha : a ≠ 0) (hd : p.coeff p.natDegree = C a) :
    (Bivariate.swap (rescale p q)).natTrailingDegree ≤ p.natDegree := by
  apply DilatedCoordinatePolynomial.trailing_degree_le_of_constant
    (p.scaleRoots (C q)) p.natDegree a ha
  rw [coeff_scaleRoots_natDegree, leadingCoeff, hd]

theorem coefficient_degree (p : Polynomial (Polynomial R)) (q : R) (c : ℕ) :
    ((Bivariate.swap (rescale p q)).coeff c).natDegree ≤ c :=
  DilatedCoordinatePolynomial.coefficient_degree (p.scaleRoots (C q)) c

theorem trailing_coordinate_degree (p : Polynomial (Polynomial R)) (q a : R)
    (ha : a ≠ 0) (hd : p.coeff p.natDegree = C a) :
    (Bivariate.swap (rescale p q)).trailingCoeff.natDegree ≤ p.natDegree :=
  (coefficient_degree p q _).trans (trailing_degree_le p q a ha hd)

/-- The additional denominator powers have an explicit original-bank height cost. -/
theorem integer_coefficient_bound (p : Polynomial (Polynomial ℤ)) (q : ℤ)
    (H L : ℕ) (hp : ∀ k j, ((p.coeff k).coeff j).natAbs ≤ 2 ^ H)
    (hq : q.natAbs ≤ 2 ^ L) (c k : ℕ) :
    (((Bivariate.swap (rescale p q)).coeff c).coeff k).natAbs ≤
      2 ^ (H + p.natDegree * L) := by
  rw [swapped_coefficient]
  split_ifs with h
  · rw [Int.natAbs_mul, Int.natAbs_pow]
    calc
      _ ≤ 2 ^ H * (2 ^ L) ^ (p.natDegree-k) := by gcongr; exact hp k (c-k)
      _ = 2 ^ (H + (p.natDegree-k) * L) := by rw [← pow_mul, ← pow_add, Nat.mul_comm L]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
        (Nat.mul_le_mul_right L (Nat.sub_le p.natDegree k)) H)
  · simp only [Int.natAbs_zero, Nat.zero_le]

end LeanCanny.Algebra.ClearedDilatedCoordinatePolynomial
