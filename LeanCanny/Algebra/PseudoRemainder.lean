/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import LeanCanny.Algebra.PrincipalQuery
import Mathlib.Tactic.Ring

/-!
# A fixed linear, division-free pseudo-remainder

Split a polynomial into coefficients below a fixed bound and its shifted high
part. The reduction step replaces each high monomial simultaneously using the
head polynomial. Repetition lowers the high degree by at least one per step.
An even number of steps provides a positive scaling for a Tarski seed.

The bound is retained under coefficient maps, including modular degree drops.
No inverse or division by a leading coefficient occurs.
-/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def high (d : ℕ) (g : R[X]) : R[X] := (Polynomial.divX^[d]) g
noncomputable def low (d : ℕ) (g : R[X]) : R[X] := g - X ^ d * high d g

theorem high_coeff (d : ℕ) (g : R[X]) (i : ℕ) :
    (high d g).coeff i = g.coeff (i + d) := by
  induction d generalizing i with
  | zero => simp [high]
  | succ d ih =>
    rw [high, Function.iterate_succ_apply', coeff_divX]
    change (high d g).coeff (i + 1) = _
    rw [ih]
    congr 1
    omega

theorem low_coeff (d : ℕ) (g : R[X]) (i : ℕ) :
    (low d g).coeff i = if i < d then g.coeff i else 0 := by
  rw [low, coeff_sub, coeff_X_pow_mul']
  by_cases hi : d ≤ i
  · simp [hi, high_coeff, Nat.sub_add_cancel hi, show ¬ i < d by omega]
  · simp [hi, show i < d by omega]

theorem low_natDegree_lt (d : ℕ) (g : R[X]) (hd : 0 < d) :
    (low d g).natDegree < d := by
  have h : (low d g).natDegree ≤ d - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [low_coeff, ite_eq_right (by omega)]
  omega

theorem high_natDegree (d : ℕ) (g : R[X]) :
    (high d g).natDegree = g.natDegree - d := by
  induction d with
  | zero => simp [high]
  | succ d ih =>
    rw [high, Function.iterate_succ_apply', natDegree_divX_eq_natDegree_tsub_one]
    change (high d g).natDegree - 1 = _
    rw [ih]
    omega

theorem high_eq_C (p : R[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    high d p = C (p.coeff d) := by
  ext i
  rw [high_coeff]
  cases i with
  | zero => simp
  | succ i =>
    rw [coeff_C, ite_eq_right (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

noncomputable def step (p : R[X]) (d : ℕ) (g : R[X]) : R[X] :=
  C (p.coeff d) * low d g - low d p * high d g

/-- The step scales its input modulo the head by the fixed leading coefficient. -/
theorem step_identity (p : R[X]) (d : ℕ) (hp : p.natDegree ≤ d) (g : R[X]) :
    step p d g = C (p.coeff d) * g - p * high d g := by
  simp only [step, low, high_eq_C p d hp]
  ring

/-- The excess-degree allowance decreases by one in each step. -/
theorem step_natDegree_le (p g : R[X]) (d e : ℕ) (hd : 0 < d)
    (hg : g.natDegree ≤ d + e) :
    (step p d g).natDegree ≤ d - 1 + e := by
  have hlp := low_natDegree_lt d p hd
  have hlg := low_natDegree_lt d g hd
  have hh : (high d g).natDegree ≤ e := by rw [high_natDegree]; omega
  have hleft : (C (p.coeff d) * low d g).natDegree ≤ d - 1 + e :=
    (natDegree_C_mul_le _ _).trans (by omega)
  have hright : (low d p * high d g).natDegree ≤ d - 1 + e :=
    natDegree_mul_le.trans (Nat.add_le_add (by omega) hh)
  exact (natDegree_sub_le _ _).trans (max_le hleft hright)

theorem iterate_natDegree_le (p g : R[X]) (d e : ℕ) (hd : 0 < d)
    (hg : g.natDegree ≤ d - 1 + e) :
    ((step p d)^[e] g).natDegree ≤ d - 1 := by
  induction e generalizing g with
  | zero => simpa using hg
  | succ e ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (step_natDegree_le p g d e hd (by omega))

theorem iterate_congruence (p g : R[X]) (d n : ℕ) (hp : p.natDegree ≤ d) :
    p ∣ C (p.coeff d ^ n) * g - (step p d)^[n] g := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha := dvd_mul_of_dvd_right ih (C (p.coeff d))
    have hb : p ∣ C (p.coeff d) * (step p d)^[n] g -
        step p d ((step p d)^[n] g) := by
      rw [step_identity p d hp]
      convert dvd_mul_right p (high d ((step p d)^[n] g)) using 1
      ring
    have hsum := dvd_add ha hb
    rw [Function.iterate_succ_apply']
    convert hsum using 1
    rw [pow_succ, map_mul]
    ring

theorem high_map (φ : R →+* S) (d : ℕ) (g : R[X]) :
    high d (g.map φ) = (high d g).map φ := by
  ext i
  simp only [high_coeff, coeff_map]

theorem low_map (φ : R →+* S) (d : ℕ) (g : R[X]) :
    low d (g.map φ) = (low d g).map φ := by
  ext i
  simp only [low_coeff, coeff_map, apply_ite φ, map_zero]

theorem step_map (φ : R →+* S) (p g : R[X]) (d : ℕ) :
    step (p.map φ) d (g.map φ) = (step p d g).map φ := by
  simp only [step, low_map, high_map, coeff_map, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C]

theorem iterate_map (φ : R →+* S) (p g : R[X]) (d n : ℕ) :
    (step (p.map φ) d)^[n] (g.map φ) = ((step p d)^[n] g).map φ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, step_map, Function.iterate_succ_apply']

noncomputable def seed (p f : R[X]) (d D : ℕ) : R[X] :=
  (step p d)^[2 * (D + 1)] (f * p.derivative)

theorem seed_natDegree_lt (p f : R[X]) (d D : ℕ) (hd : 0 < d)
    (hD : (f * p.derivative).natDegree ≤ D) :
    (seed p f d D).natDegree < d := by
  have h := iterate_natDegree_le p (f * p.derivative) d (2 * (D + 1)) hd (by omega)
  change ((step p d)^[2 * (D + 1)] (f * p.derivative)).natDegree < d
  omega

theorem seed_map (φ : R →+* S) (p f : R[X]) (d D : ℕ) :
    seed (p.map φ) (f.map φ) d D = (seed p f d D).map φ := by
  simp only [seed, Polynomial.derivative_map, ← Polynomial.map_mul, iterate_map]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Even powering gives the positive congruence required for a Tarski seed. -/
theorem isTarskiSeed (p f : K[X]) (d D : ℕ) (hp : p.natDegree = d) (hn : p ≠ 0) :
    Sturm.IsTarskiSeed p f (seed p f d D) := by
  have ha : p.coeff d ≠ 0 := by rw [← hp, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hn
  have hpos : 0 < p.coeff d ^ (2 * (D + 1)) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero ha) _
  obtain ⟨u, hu⟩ := iterate_congruence p (f * p.derivative) d (2 * (D + 1)) hp.le
  refine Sturm.IsTarskiSeed.of_identity (p.coeff d ^ (2 * (D + 1))) 1 u hpos zero_lt_one ?_
  change C _ * _ = u * p + C 1 * (step p d)^[2 * (D + 1)] _
  rw [map_one, one_mul]
  linear_combination hu

end LeanCanny.Algebra.PseudoRemainder
