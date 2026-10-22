/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSign
public import LeanCanny.Algebra.PseudoRemainderBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # An explicit small-parameter sign bound for integer polynomials

Coefficient mass bounds evaluation on the real unit interval. After factoring
the lowest power, the nonzero integer constant coefficient has magnitude at
least one, so a tail of magnitude less than one preserves its sign.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalSign
open Polynomial
open scoped BigOperators

theorem abs_eval_le_mass (p : ℤ[X]) (x : ℝ) (hx : |x| ≤ 1) :
    |p.eval₂ (Int.castRingHom ℝ) x| ≤ (coefficientMass p : ℝ) := by
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, Int.coe_castRingHom]
  calc
    _ ≤ ∑ i ∈ p.support, |(p.coeff i : ℝ) * x ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ p.support, |(p.coeff i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg x) hx)
    _ = _ := by
      simp only [coefficientMass, Polynomial.sum, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]

theorem sign_eval_eq_constant_of_small (p : ℤ[X]) (x : ℝ) (hp : p.coeff 0 ≠ 0)
    (hx : 0 < x) (hx1 : x ≤ 1) (hsmall : x * (coefficientMass p : ℝ) < 1) :
    SignType.sign (p.eval₂ (Int.castRingHom ℝ) x) = SignType.sign (p.coeff 0) := by
  let t := PseudoRemainder.high 1 p
  have ht : |t.eval₂ (Int.castRingHom ℝ) x| ≤ (coefficientMass p : ℝ) := by
    apply (abs_eval_le_mass t x (by rw [abs_of_pos hx]; exact hx1)).trans
    exact_mod_cast PseudoRemainder.high_mass_le p 1
  have hd : |x * t.eval₂ (Int.castRingHom ℝ) x| < 1 := by
    rw [abs_mul, abs_of_pos hx]
    exact (mul_le_mul_of_nonneg_left ht hx.le).trans_lt hsmall
  have he : p.eval₂ (Int.castRingHom ℝ) x = (p.coeff 0 : ℝ) + x * t.eval₂ (Int.castRingHom ℝ) x := by
    have h := Polynomial.X_mul_divX_add p
    have hv := congrArg (fun q : ℤ[X] => q.eval₂ (Int.castRingHom ℝ) x) h
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Int.coe_castRingHom, t, PseudoRemainder.high, Function.iterate_one, add_comm] using hv.symm
  rw [he]
  rcases lt_or_gt_of_ne hp with hn | hp
  · rw [sign_neg hn]
    apply sign_neg
    have hc : (p.coeff 0 : ℝ) ≤ -1 := by exact_mod_cast (show p.coeff 0 ≤ -1 by omega)
    have hb := le_abs_self (x * t.eval₂ (Int.castRingHom ℝ) x)
    linarith
  · rw [sign_pos hp]
    apply sign_pos
    have hc : (1 : ℝ) ≤ (p.coeff 0 : ℝ) := by exact_mod_cast (show 1 ≤ p.coeff 0 by omega)
    have hb := neg_abs_le (x * t.eval₂ (Int.castRingHom ℝ) x)
    linarith

theorem integer_sign_eval_of_small (p : ℤ[X]) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hsmall : x * (coefficientMass p : ℝ) < 1) :
    SignType.sign (p.eval₂ (Int.castRingHom ℝ) x) = SignType.sign p.trailingCoeff := by
  by_cases hp : p = 0
  · subst p
    simp
  let t := p.natTrailingDegree
  let q := PseudoRemainder.high t p
  have hl : PseudoRemainder.low t p = 0 := by
    ext i
    rw [PseudoRemainder.low_coeff, Polynomial.coeff_zero]
    split_ifs with hi
    · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
    · rfl
  have hf : p = X ^ t * q := sub_eq_zero.mp hl
  have hc : q.coeff 0 = p.trailingCoeff := by
    rw [PseudoRemainder.high_coeff, Nat.zero_add]
    rfl
  have hq : q.coeff 0 ≠ 0 := by rw [hc]; exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
  have hm : coefficientMass q ≤ coefficientMass p := PseudoRemainder.high_mass_le _ _
  have hs : x * (coefficientMass q : ℝ) < 1 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hm) hx.le).trans_lt hsmall
  have hsign := sign_eval_eq_constant_of_small q x hq hx hx1 hs
  have he : p.eval₂ (Int.castRingHom ℝ) x = x ^ t * q.eval₂ (Int.castRingHom ℝ) x := by
    conv_lhs => rw [hf]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [he, sign_mul, sign_pos (pow_pos hx _), one_mul, hsign, hc]

noncomputable def dyadic (s : ℕ) : ℝ := ((2 : ℝ) ^ s)⁻¹

theorem dyadic_pos (s : ℕ) : 0 < dyadic s := inv_pos.mpr (pow_pos (by norm_num) _)

theorem dyadic_le_one (s : ℕ) : dyadic s ≤ 1 :=
  (inv_le_one₀ (pow_pos (by norm_num) s)).mpr (one_le_pow₀ (by norm_num))

theorem dyadic_mul_mass_lt_one (p : ℤ[X]) (b s : ℕ)
    (hm : coefficientMass p ≤ 2 ^ b) (hs : b < s) : dyadic s * (coefficientMass p : ℝ) < 1 := by
  have hc : (coefficientMass p : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast hm
  have hp : (2 : ℝ) ^ b < (2 : ℝ) ^ s := pow_lt_pow_right₀ (by norm_num) hs
  unfold dyadic
  rw [mul_comm, ← div_eq_mul_inv, div_lt_one (pow_pos (by norm_num) s)]
  exact hc.trans_lt hp

/-- One dyadic interval works uniformly for every polynomial with the same mass bound. -/
theorem integer_sign_eval_le_dyadic (p : ℤ[X]) (b s : ℕ)
    (hm : coefficientMass p ≤ 2 ^ b) (hs : b < s) (x : ℝ) (hx : 0 < x) (hxs : x ≤ dyadic s) :
    SignType.sign (p.eval₂ (Int.castRingHom ℝ) x) = SignType.sign p.trailingCoeff := by
  apply integer_sign_eval_of_small p x hx (hxs.trans (dyadic_le_one s))
  exact (mul_le_mul_of_nonneg_right hxs (Nat.cast_nonneg _)).trans_lt
    (dyadic_mul_mass_lt_one p b s hm hs)

theorem integer_sign_eval_dyadic (p : ℤ[X]) (b s : ℕ)
    (hm : coefficientMass p ≤ 2 ^ b) (hs : b < s) :
    SignType.sign (p.eval₂ (Int.castRingHom ℝ) (dyadic s)) = SignType.sign p.trailingCoeff :=
  integer_sign_eval_le_dyadic p b s hm hs _ (dyadic_pos s) le_rfl

end LeanCanny.Algebra.InfinitesimalSign
