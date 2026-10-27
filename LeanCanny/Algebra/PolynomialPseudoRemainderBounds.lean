/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialKronecker
public import LeanCanny.Algebra.NestedCoefficientMass

/-! # Coefficient bounds for fixed polynomial reductions

The declared reduction degree is arbitrary. Parameter degrees grow linearly
with the number of steps; total coefficient mass has an explicit exponential
bound. Neither estimate assumes stability of the head's symbolic degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial
open scoped Classical

theorem mul_parameter_degree {R : Type*} [CommRing R] (p q : (R[X])[X]) (P Q : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (hq : ∀ i, (q.coeff i).natDegree ≤ Q) :
    ∀ i, ((p * q).coeff i).natDegree ≤ P + Q := by
  apply (PolynomialKronecker.inner_degree_iff_swap (p * q) (P + Q)).mpr
  rw [map_mul]
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
    ((PolynomialKronecker.inner_degree_iff_swap p P).mp hp)
    ((PolynomialKronecker.inner_degree_iff_swap q Q).mp hq))

theorem low_parameter_degree {R : Type*} [CommRing R] (p : (R[X])[X]) (d P : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (i : ℕ) : ((low d p).coeff i).natDegree ≤ P := by
  rw [low_coeff]
  split_ifs
  · exact hp i
  · simp

theorem high_parameter_degree {R : Type*} [CommRing R] (p : (R[X])[X]) (d P : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (i : ℕ) : ((high d p).coeff i).natDegree ≤ P := by
  rw [high_coeff]
  exact hp _

theorem derivative_parameter_degree {R : Type*} [CommRing R] (p : (R[X])[X]) (P : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (i : ℕ) : (p.derivative.coeff i).natDegree ≤ P := by
  have hd : p.derivative.coeff i = p.coeff (i + 1) * ((i + 1 : ℕ) : R[X]) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Polynomial.coeff_derivative p i
  rw [hd]
  exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_natCast, add_zero] using hp (i + 1))

theorem step_parameter_degree {R : Type*} [CommRing R] (p g : (R[X])[X]) (d P G : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (hg : ∀ i, (g.coeff i).natDegree ≤ G) (i : ℕ) :
    ((step p d g).coeff i).natDegree ≤ P + G := by
  rw [step, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp d) (low_parameter_degree g d G hg i))
  · exact mul_parameter_degree (low d p) (high d g) P G
      (low_parameter_degree p d P hp) (high_parameter_degree g d G hg) i

theorem iterate_parameter_degree {R : Type*} [CommRing R] (p g : (R[X])[X]) (d n P G : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (hg : ∀ i, (g.coeff i).natDegree ≤ G) :
    ∀ i, (((step p d)^[n] g).coeff i).natDegree ≤ n * P + G := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    intro i
    rw [Function.iterate_succ_apply']
    have h := step_parameter_degree p ((step p d)^[n] g) d P (n * P + G) hp ih i
    rw [Nat.succ_mul]
    omega

theorem seed_parameter_degree {R : Type*} [CommRing R] (p q : (R[X])[X]) (d D P Q : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ P) (hq : ∀ i, (q.coeff i).natDegree ≤ Q) (i : ℕ) :
    ((seed p q d D).coeff i).natDegree ≤ 2 * (D + 1) * P + (Q + P) :=
  iterate_parameter_degree p (q * p.derivative) d (2 * (D + 1)) P (Q + P) hp
    (mul_parameter_degree q p.derivative Q P hq (derivative_parameter_degree p P hp)) i

theorem iterate_mass_le_pow (p g : (ℤ[X])[X]) (d n bp bg : ℕ)
    (hp : NestedMass.mass p ≤ 2 ^ bp) (hg : NestedMass.mass g ≤ 2 ^ bg) :
    NestedMass.mass ((step p d)^[n] g) ≤ 2 ^ (n * (bp + 1) + bg) := by
  calc
    _ ≤ (2 * NestedMass.mass p) ^ n * NestedMass.mass g := NestedMass.iterate_le p g d n
    _ ≤ (2 * 2 ^ bp) ^ n * 2 ^ bg := Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hp) n) hg
    _ = _ := by rw [← pow_succ', ← pow_mul, ← pow_add, Nat.mul_comm (bp + 1) n]

def fixedSeedMassBound (D dp bp bq : ℕ) : ℕ := 2 * (D + 1) * (bp + 1) + bq + dp.size + bp

theorem seed_mass_le_pow (p q : (ℤ[X])[X]) (d D dp bp bq : ℕ)
    (hdp : p.natDegree ≤ dp) (hp : NestedMass.mass p ≤ 2 ^ bp) (hq : NestedMass.mass q ≤ 2 ^ bq) :
    NestedMass.mass (seed p q d D) ≤ 2 ^ fixedSeedMassBound D dp bp bq := by
  have hprod : NestedMass.mass (q * p.derivative) ≤ 2 ^ (bq + dp.size + bp) := by
    calc
      _ ≤ NestedMass.mass q * (p.natDegree * NestedMass.mass p) :=
        (NestedMass.mul_le _ _).trans (Nat.mul_le_mul_left _ (NestedMass.derivative_le p))
      _ ≤ 2 ^ bq * (2 ^ dp.size * 2 ^ bp) := Nat.mul_le_mul hq
        (Nat.mul_le_mul (hdp.trans (Nat.lt_size_self dp).le) hp)
      _ = _ := by rw [← pow_add, ← pow_add, Nat.add_assoc]
  have h := iterate_mass_le_pow p (q * p.derivative) d (2 * (D + 1)) bp (bq + dp.size + bp) hp hprod
  simpa only [seed, fixedSeedMassBound, Nat.add_assoc] using h

end LeanCanny.Algebra.PseudoRemainder
