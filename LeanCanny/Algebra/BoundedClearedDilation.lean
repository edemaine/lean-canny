/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedDilatedCoordinatePolynomial

/-! # Denominator clearing at the known original coordinate-degree bound

The modular algorithm uses the explicit original degree allowance, rather
than computing a degree in the retained algebra. This also gives one total
polynomial when different retained components have different degrees.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedClearedDilation
open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def rescale (p : Polynomial (Polynomial R)) (q : R) (d : ℕ) :
    Polynomial (Polynomial R) :=
  C (C (q ^ (d-p.natDegree))) * ClearedDilatedCoordinatePolynomial.rescale p q

theorem coefficient (p : Polynomial (Polynomial R)) (q : R) (d : ℕ)
    (hp : p.natDegree ≤ d) (c k : ℕ) :
    ((rescale p q d).coeff k).coeff c =
      if k ≤ c then (p.coeff k).coeff (c-k) * q ^ (d-k) else 0 := by
  rw [rescale, coeff_C_mul, coeff_C_mul, ClearedDilatedCoordinatePolynomial.coefficient]
  split_ifs
  · by_cases hk : k ≤ p.natDegree
    · calc
        _ = (p.coeff k).coeff (c-k) * q ^ ((d-p.natDegree)+(p.natDegree-k)) := by
          rw [pow_add]
          ring
        _ = _ := by rw [show (d-p.natDegree)+(p.natDegree-k)=d-k by omega]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k), coeff_zero]
      simp only [zero_mul, mul_zero]
  · exact mul_zero _

theorem swapped_coefficient (p : Polynomial (Polynomial R)) (q : R) (d : ℕ)
    (hp : p.natDegree ≤ d) (c k : ℕ) :
    ((Bivariate.swap (rescale p q d)).coeff c).coeff k =
      if k ≤ c then (p.coeff k).coeff (c-k) * q ^ (d-k) else 0 := by
  rw [DilatedCoordinatePolynomial.swap_coefficient, coefficient p q d hp]

theorem root {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Polynomial (Polynomial R)) (q : R) (d : ℕ) (e y x : S)
    (hy : φ q * y = e*x) (hp : eval₂ (eval₂RingHom φ e) y p = 0) :
    eval₂ (eval₂RingHom φ e) x (rescale p q d) = 0 := by
  rw [rescale, eval₂_mul, ClearedDilatedCoordinatePolynomial.root φ p q e y x hy hp, mul_zero]

theorem trailing_degree_le (p : Polynomial (Polynomial R)) (q a : R) (d : ℕ)
    (hp : p.natDegree ≤ d) (ha : a ≠ 0) (hd : p.coeff d = C a) :
    (Bivariate.swap (rescale p q d)).natTrailingDegree ≤ d := by
  apply natTrailingDegree_le_of_ne_zero
  intro hz
  have H := congrArg (fun f : Polynomial R => f.coeff d) hz
  rw [swapped_coefficient p q d hp, ite_eq_left (Nat.le_refl d), Nat.sub_self,
    hd, coeff_C_zero, pow_zero, mul_one, coeff_zero] at H
  exact ha H

theorem coefficient_degree (p : Polynomial (Polynomial R)) (q : R) (d c : ℕ)
    (hp : p.natDegree ≤ d) :
    ((Bivariate.swap (rescale p q d)).coeff c).natDegree ≤ c := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [swapped_coefficient p q d hp, ite_eq_right (by omega : ¬k ≤ c)]

end LeanCanny.Algebra.BoundedClearedDilation
