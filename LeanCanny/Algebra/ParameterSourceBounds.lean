/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.Algebra.ParameterizedSignPatterns
import Mathlib.Tactic.Ring

/-! # Small-parameter test bounds from original bivariate sources

Outer degree and total coefficient-mass bounds suffice for the symbolic seed
and every principal test. Uniform bounds for ternary products avoid enumerating
their test polynomials when choosing the small parameter.
-/

@[expose] public section

namespace LeanCanny.Algebra.ParameterTarski
open Polynomial PrincipalSubresultant RootSignQueries
open scoped BigOperators

def seedMassBound (dp df bp bf : ℕ) : ℕ := 2 * (dp + df + 1) * (bp + 1) + bf + dp.size + bp

def sourceBound (dp df bp bf : ℕ) : ℕ := parameterMassBound (2 * dp) (bp + seedMassBound dp df bp bf)

theorem seed_mass_le (p f : (ℤ[X])[X]) (dp df bp bf : ℕ)
    (hdp : p.natDegree ≤ dp) (hdf : f.natDegree ≤ df)
    (hp : NestedMass.mass p ≤ 2 ^ bp) (hf : NestedMass.mass f ≤ 2 ^ bf) :
    NestedMass.mass (seed p f) ≤ 2 ^ seedMassBound dp df bp bf := by
  have hprod : NestedMass.mass (f * p.derivative) ≤ 2 ^ bf * (2 ^ dp.size * 2 ^ bp) :=
    (NestedMass.mul_le _ _).trans (Nat.mul_le_mul hf
      ((NestedMass.derivative_le p).trans (Nat.mul_le_mul (hdp.trans (Nat.lt_size_self dp).le) hp)))
  have hn : 2 * (p.natDegree + f.natDegree + 1) ≤ 2 * (dp + df + 1) := by omega
  calc
    _ ≤ (2 * NestedMass.mass p) ^ (2 * (p.natDegree + f.natDegree + 1)) * NestedMass.mass (f * p.derivative) :=
      NestedMass.iterate_le _ _ _ _
    _ ≤ (2 * 2 ^ bp) ^ (2 * (p.natDegree + f.natDegree + 1)) * (2 ^ bf * (2 ^ dp.size * 2 ^ bp)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hp) _) hprod
    _ = 2 ^ (2 * (p.natDegree + f.natDegree + 1) * (bp + 1) + bf + dp.size + bp) := by
      rw [← pow_succ', ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have := Nat.mul_le_mul_right (bp + 1) hn
      unfold seedMassBound
      omega)

theorem seed_natDegree_le (p f : (ℤ[X])[X]) : (seed p f).natDegree ≤ p.natDegree := by
  by_cases hd : p.natDegree = 0
  · have hl : ∀ g : (ℤ[X])[X], PseudoRemainder.low 0 g = 0 := by
      intro g
      apply Polynomial.ext
      intro i
      simp only [PseudoRemainder.low_coeff, Nat.not_lt_zero, ↓reduceIte, coeff_zero]
    have hs : ∀ g : (ℤ[X])[X], PseudoRemainder.step p 0 g = 0 := by
      intro g
      simp only [PseudoRemainder.step, hl, mul_zero, zero_mul, sub_self]
    unfold seed PseudoRemainder.seed
    rw [hd, zero_add, show 2 * (f.natDegree + 1) = (2 * f.natDegree + 1) + 1 by omega,
      Function.iterate_succ_apply', hs, natDegree_zero]
  · apply Nat.le_of_lt
    apply PseudoRemainder.seed_natDegree_lt _ _ _ _ (by omega)
    have hh := (natDegree_derivative_le p).trans (Nat.sub_le _ _)
    exact natDegree_mul_le.trans (by omega)

theorem bounded_of_mass (p f : (ℤ[X])[X]) (dp df bp bf : ℕ)
    (hdp : p.natDegree ≤ dp) (hdf : f.natDegree ≤ df)
    (hp : NestedMass.mass p ≤ 2 ^ bp) (hf : NestedMass.mass f ≤ 2 ^ bf) :
    Bounded p f (sourceBound dp df bp bf) := by
  have hseed := seed_mass_le p f dp df bp bf hdp hdf hp hf
  let a := bp + seedMassBound dp df bp bf
  have hp' : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ a := fun i =>
    ((NestedMass.coeff_le p i).trans hp).trans (Nat.pow_le_pow_right (by decide) (by dsimp [a]; omega))
  have hq' : ∀ i, coefficientMass ((seed p f).coeff i) ≤ 2 ^ a := fun i =>
    ((NestedMass.coeff_le (seed p f) i).trans hseed).trans (Nat.pow_le_pow_right (by decide) (by dsimp [a]; omega))
  have ha : 2 ^ a ≤ 2 ^ sourceBound dp df bp bf := Nat.pow_le_pow_right (by decide) (by
    unfold sourceBound parameterMassBound
    dsimp [a]
    omega)
  constructor
  · exact (hp' p.natDegree).trans ha
  · exact (hq' (seed p f).natDegree).trans ha
  · intro j _
    exact signedPsc_mass_le p (seed p f) _ _ j (2 * dp) a (by have := seed_natDegree_le p f; omega) hp' hq'

theorem bounded_of_coeff (p f : (ℤ[X])[X]) (dp df bp bf : ℕ)
    (hdp : p.natDegree ≤ dp) (hdf : f.natDegree ≤ df)
    (hp : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ bp)
    (hf : ∀ i, coefficientMass (f.coeff i) ≤ 2 ^ bf) :
    Bounded p f (sourceBound dp df (bp + (dp + 1).size) (bf + (df + 1).size)) :=
  bounded_of_mass p f _ _ _ _ hdp hdf (NestedMass.le_pow p dp bp hdp hp) (NestedMass.le_pow f df bf hdf hf)

def patternSourceBound (dp D k bp bf : ℕ) : ℕ :=
  sourceBound dp (2 * k * D) (bp + (dp + 1).size) (2 * k * (bf + (D + 1).size))

theorem queryProduct_mass_le {J : Type*} [Fintype J] (Q : J → (ℤ[X])[X]) (e : J → Fin 3) (b : ℕ)
    (hQ : ∀ i, NestedMass.mass (Q i) ≤ 2 ^ b) :
    NestedMass.mass (queryPolynomial Q e) ≤ 2 ^ (2 * Fintype.card J * b) := by
  classical
  calc
    _ ≤ ∏ i, NestedMass.mass (Q i ^ (e i).val) := NestedMass.prod_le _ _
    _ ≤ ∏ i : J, 2 ^ (2 * b) := by
      apply Finset.prod_le_prod
      intro i _
      apply (NestedMass.pow_le (Q i) _).trans
      apply (Nat.pow_le_pow_left (hQ i) _).trans
      rw [← pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      have hi : (e i).val ≤ 2 := by have := (e i).isLt; omega
      have hm := Nat.mul_le_mul_left b hi
      omega
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]; congr 1; ring

theorem pattern_bounded_of_coeff {J : Type*} [Fintype J] (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X])
    (dp D bp bf : ℕ) (hpD : p.natDegree ≤ dp) (hQD : ∀ i, (Q i).natDegree ≤ D)
    (hp : ∀ j, coefficientMass (p.coeff j) ≤ 2 ^ bp)
    (hQ : ∀ i j, coefficientMass ((Q i).coeff j) ≤ 2 ^ bf) (e : J → Fin 3) :
    Bounded p (queryPolynomial Q e) (patternSourceBound dp D (Fintype.card J) bp bf) :=
  bounded_of_mass p (queryPolynomial Q e) _ _ _ _ hpD (natDegree_queryPolynomial_le Q e D hQD)
    (NestedMass.le_pow p dp bp hpD hp)
    (queryProduct_mass_le Q e _ (fun i => NestedMass.le_pow (Q i) D bf (hQD i) (hQ i)))

end LeanCanny.Algebra.ParameterTarski
