/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ReciprocalEquation

/-! # Uniform integer coefficient bounds for reciprocal equations -/

@[expose] public section

namespace LeanCanny.Algebra.ReciprocalEquation
open MvPolynomial
open scoped Classical

variable {σ : Type*}

theorem derivative_coefficient_bound (p : MvPolynomial σ ℤ) (base : σ) (D H : ℕ)
    (hD : p.totalDegree ≤ D) (hH : ∀ e, (p.coeff e).natAbs ≤ H) (e : σ →₀ ℕ) :
    ((pderiv base p).coeff e).natAbs ≤ D * H := by
  rw [MvPolynomial.coeff_pderiv, Int.natAbs_mul,
    show (e base : ℤ) + 1 = ((e base + 1 : ℕ) : ℤ) from (Nat.cast_add _ _).symm, Int.natAbs_natCast]
  by_cases hz : p.coeff (e + Finsupp.single base 1) = 0
  · simp [hz]
  · have hd := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hz)).trans hD
    have hi := Finsupp.le_degree base (e + Finsupp.single base 1)
    change (e + Finsupp.single base 1).degree ≤ D at hd
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hi
    have he : e base + 1 ≤ D := hi.trans hd
    exact (Nat.mul_le_mul (hH _) he).trans_eq (Nat.mul_comm H D)

theorem coefficient_bound (p : MvPolynomial σ ℤ) (base : σ) (D H : ℕ)
    (hD : p.totalDegree ≤ D) (hH : ∀ e, (p.coeff e).natAbs ≤ H) (m : Option σ →₀ ℕ) :
    ((polynomial p base).coeff m).natAbs ≤ D * H + 1 := by
  rw [coefficient]
  apply (Int.natAbs_sub_le _ _).trans
  apply Nat.add_le_add
  · split_ifs
    · exact derivative_coefficient_bound p base D H hD hH m.some
    · exact Nat.zero_le _
  · split_ifs <;> decide

theorem coefficient_pow_bound (p : MvPolynomial σ ℤ) (base : σ) (D B : ℕ)
    (hD : p.totalDegree ≤ D) (hB : ∀ e, (p.coeff e).natAbs ≤ 2 ^ B) (m : Option σ →₀ ℕ) :
    ((polynomial p base).coeff m).natAbs ≤ 2 ^ (B + D + 1) := by
  apply (coefficient_bound p base D (2 ^ B) hD hB m).trans
  have hd : D ≤ 2 ^ D := Nat.lt_two_pow_self.le
  have hpos : 1 ≤ 2 ^ (B + D) := Nat.one_le_two_pow
  have hm : D * 2 ^ B ≤ 2 ^ (B + D) := by
    calc
      _ ≤ 2 ^ D * 2 ^ B := Nat.mul_le_mul_right _ hd
      _ = _ := by rw [← pow_add, Nat.add_comm]
  rw [pow_succ]
  omega

end LeanCanny.Algebra.ReciprocalEquation
