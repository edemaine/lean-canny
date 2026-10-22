/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainder
public import LeanCanny.Algebra.CoefficientMass
import Mathlib.Tactic.Ring

/-! # Integer bit budgets for the division-free reduction -/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial
open scoped BigOperators

private theorem mass_range (g : ℤ[X]) (N : ℕ) (hN : g.natDegree < N) :
    coefficientMass g = ∑ i ∈ Finset.range N, (g.coeff i).natAbs :=
  g.sum_over_range' (fun _ => rfl) N hN

private theorem mass_mono_coeff (f g : ℤ[X])
    (h : ∀ i, (f.coeff i).natAbs ≤ (g.coeff i).natAbs) :
    coefficientMass f ≤ coefficientMass g := by
  let N := max f.natDegree g.natDegree + 1
  rw [mass_range f N (by dsimp [N]; omega), mass_range g N (by dsimp [N]; omega)]
  exact Finset.sum_le_sum fun i _ => h i

theorem low_mass_le (g : ℤ[X]) (d : ℕ) : coefficientMass (low d g) ≤ coefficientMass g := by
  apply mass_mono_coeff
  intro i
  rw [low_coeff]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem high_mass_le (g : ℤ[X]) (d : ℕ) : coefficientMass (high d g) ≤ coefficientMass g := by
  by_cases hd : d ≤ g.natDegree
  · let N := g.natDegree - d + 1
    have hN : g.natDegree + 1 = d + N := by dsimp [N]; omega
    rw [mass_range (high d g) N (by rw [high_natDegree]; dsimp [N]; omega)]
    simp only [high_coeff]
    have he : coefficientMass g =
        (∑ i ∈ Finset.range d, (g.coeff i).natAbs) +
          ∑ i ∈ Finset.range N, (g.coeff (i + d)).natAbs := by
      rw [mass_range g (g.natDegree + 1) (by omega), hN, Finset.sum_range_add]
      simp only [Nat.add_comm]
    rw [he]
    omega
  · have hz : high d g = 0 := by
      ext i
      rw [high_coeff, coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, coefficientMass_zero]
    exact Nat.zero_le _

private theorem mass_neg (g : ℤ[X]) : coefficientMass (-g) = coefficientMass g := by
  rw [mass_range (-g) (g.natDegree + 1) (by rw [natDegree_neg]; omega),
    mass_range g (g.natDegree + 1) (by omega)]
  simp only [coeff_neg, Int.natAbs_neg]

theorem step_mass_le (p g : ℤ[X]) (d : ℕ) :
    coefficientMass (step p d g) ≤ 2 * coefficientMass p * coefficientMass g := by
  have hsub (f h : ℤ[X]) : coefficientMass (f - h) ≤ coefficientMass f + coefficientMass h := by
    simpa only [sub_eq_add_neg, mass_neg] using coefficientMass_add_le f (-h)
  calc
    _ ≤ coefficientMass (C (p.coeff d) * low d g) + coefficientMass (low d p * high d g) := hsub _ _
    _ ≤ ((p.coeff d).natAbs * coefficientMass (low d g)) +
        coefficientMass (low d p) * coefficientMass (high d g) := by
      exact Nat.add_le_add (by simpa only [coefficientMass_C] using coefficientMass_mul_le (C (p.coeff d)) (low d g))
        (coefficientMass_mul_le (low d p) (high d g))
    _ ≤ coefficientMass p * coefficientMass g + coefficientMass p * coefficientMass g :=
      Nat.add_le_add (Nat.mul_le_mul (coeff_natAbs_le_coefficientMass p d) (low_mass_le g d))
        (Nat.mul_le_mul (low_mass_le p d) (high_mass_le g d))
    _ = _ := by ring

theorem iterate_mass_le (p g : ℤ[X]) (d n : ℕ) :
    coefficientMass ((step p d)^[n] g) ≤
      (2 * coefficientMass p) ^ n * coefficientMass g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact (step_mass_le p _ d).trans (by
      simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * coefficientMass p) ih)

theorem iterate_coeff_size_le (p g : ℤ[X]) (d n bp bg i : ℕ)
    (hp : coefficientMass p ≤ 2 ^ bp) (hg : coefficientMass g ≤ 2 ^ bg) :
    (((step p d)^[n] g).coeff i).natAbs.size ≤ n * (bp + 1) + bg + 1 := by
  have h : (((step p d)^[n] g).coeff i).natAbs ≤ 2 ^ (n * (bp + 1) + bg) := by
    calc
      _ ≤ coefficientMass ((step p d)^[n] g) := coeff_natAbs_le_coefficientMass _ _
      _ ≤ (2 * coefficientMass p) ^ n * coefficientMass g := iterate_mass_le p g d n
      _ ≤ (2 * 2 ^ bp) ^ n * 2 ^ bg :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hp) _) hg
      _ = _ := by rw [← pow_succ', ← pow_mul, ← pow_add]; congr 1; ring
  simpa only [Nat.size_pow] using Nat.size_le_size h

end LeanCanny.Algebra.PseudoRemainder
