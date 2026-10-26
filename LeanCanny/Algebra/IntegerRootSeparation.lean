/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantNonvanishing
public import LeanCanny.Algebra.CannyResultantBudget
public import LeanCanny.Algebra.PolynomialSignedReflection
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Algebra.IntegerRootBound
public import Mathlib.Algebra.Polynomial.Reverse

/-! # Explicit separation of distinct real roots of an integer polynomial

The difference resultant annihilates every root difference, even when the
input has repeated roots. Applying the integer Cauchy bound to its reciprocal
gives a dyadic separation exponent with a native binary writer.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerRootSeparation
open Polynomial
open scoped Classical

noncomputable def difference (p : ℤ[X]) : ℤ[X] := cannyResultant p (p.comp (-X)) 1

def coefficientBudget (D B : ℕ) : ℕ := CannyResultantBits.coefficientBudget D D 1 B B
def precision (D B : ℕ) : ℕ := coefficientBudget D B + (D * D + 1).size + 1

theorem precision_binary {D B : List Bool → ℕ} (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun c => precision (D c) (B c)) :=
  ((CannyResultantBits.coefficientBudget_binary hD hD (BinaryFn.const 1) hB hB).add
    (((hD.mul hD).add (BinaryFn.const 1)).size)).add (BinaryFn.const 1)

theorem ne_zero (p : ℤ[X]) (hp : p ≠ 0) : difference p ≠ 0 :=
  ResultantNonvanishing.integer_ne_zero p (p.comp (-X)) 1 hp (Polynomial.comp_neg_X_eq_zero_iff.not.mpr hp)

theorem eval_difference (p : ℤ[X]) (hp : p ≠ 0) (a b : ℝ)
    (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) (hb : p.eval₂ (Int.castRingHom ℝ) b = 0) :
    (difference p).eval₂ (Int.castRingHom ℝ) (a - b) = 0 := by
  have hb' : (p.comp (-X)).eval₂ (Int.castRingHom ℝ) (-b) = 0 := by
    simpa only [Polynomial.eval₂_comp, Polynomial.eval₂_neg, Polynomial.eval₂_X, neg_neg] using hb
  simpa only [difference, Nat.cast_one, one_mul, sub_eq_add_neg] using
    ResultantNonvanishing.integer_sum_root p (p.comp (-X)) 1 a (-b)
      (Polynomial.comp_neg_X_eq_zero_iff.not.mpr hp) ha hb'

theorem reflected_degree (p : ℤ[X]) : (p.comp (-X)).natDegree = p.natDegree := by
  simp only [Polynomial.natDegree_comp, Polynomial.natDegree_neg, Polynomial.natDegree_X, Nat.mul_one]

theorem reflected_coefficient (p : ℤ[X]) (k : ℕ) : ((p.comp (-X)).coeff k).natAbs = (p.coeff k).natAbs := by
  rw [PolynomialSignedReflection.coefficient]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]

theorem degree_le (p : ℤ[X]) (D : ℕ) (hD : p.natDegree ≤ D) : (difference p).natDegree ≤ D * D :=
  (cannyResultant_natDegree_le p (p.comp (-X)) 1).trans (by rw [reflected_degree]; exact Nat.mul_le_mul hD hD)

theorem coefficient_bits (p : ℤ[X]) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ k, (p.coeff k).natAbs ≤ 2 ^ B) (k : ℕ) :
    ((difference p).coeff k).natAbs.size ≤ coefficientBudget D B :=
  CannyResultantBits.coefficient_size_le p (p.comp (-X)) 1 D D 1 B B k hD
    (by rw [reflected_degree]; exact hD) le_rfl hB (fun i => by rw [reflected_coefficient]; exact hB i)

theorem reverse_mass (p : ℤ[X]) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ k, (p.coeff k).natAbs ≤ 2 ^ B) :
    coefficientMass (difference p).reverse ≤ 2 ^ (coefficientBudget D B + (D * D + 1).size) := by
  apply coefficientMass_le_pow_of_degree_coeff _ (D * D) (coefficientBudget D B)
    ((Polynomial.reverse_natDegree_le _).trans (degree_le p D hD))
  intro k
  rw [Polynomial.coeff_reverse]
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (coefficient_bits p D B hD hB _))

theorem separated (p : ℤ[X]) (hp : p ≠ 0) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ k, (p.coeff k).natAbs ≤ 2 ^ B) (a b : ℝ) (hab : a ≠ b)
    (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) (hb : p.eval₂ (Int.castRingHom ℝ) b = 0) :
    ((2 : ℝ) ^ precision D B)⁻¹ < |a - b| := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  let : Invertible (a - b) := invertibleOfNonzero hd
  have hr : (difference p).reverse.eval₂ (Int.castRingHom ℝ) (a - b)⁻¹ = 0 := by
    simpa only [invOf_eq_inv] using
      (Polynomial.eval₂_reverse_eq_zero_iff (Int.castRingHom ℝ) (a - b) (difference p)).mpr
        (eval_difference p hp a b ha hb)
  have hn : (difference p).reverse ≠ 0 := Polynomial.reverse_eq_zero.not.mpr (ne_zero p hp)
  have hc := abs_root_lt_coefficientMass_add_one (difference p).reverse hn ((a - b)⁻¹) hr
  have hm : (coefficientMass (difference p).reverse : ℝ) + 1 ≤ (2 : ℝ) ^ precision D B := by
    have hmass := reverse_mass p D B hD hB
    have hpos := Nat.one_le_two_pow (n := coefficientBudget D B + (D * D + 1).size)
    have hnat : coefficientMass (difference p).reverse + 1 ≤ 2 ^ precision D B := by
      unfold precision
      rw [pow_succ]
      omega
    exact_mod_cast hnat
  have hg : |a - b|⁻¹ < (2 : ℝ) ^ precision D B := by simpa only [abs_inv] using hc.trans_le hm
  exact (inv_lt_comm₀ (abs_pos.mpr hd) (pow_pos (by norm_num) _)).mp hg

end LeanCanny.Algebra.IntegerRootSeparation
