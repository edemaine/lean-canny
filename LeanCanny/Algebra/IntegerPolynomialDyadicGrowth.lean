/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialOuterSign

/-! # Polynomial degree from actual growth at dyadic integer inputs

A positive leading term cannot remain below a smaller fixed power at all
sufficiently large dyadic inputs. The auxiliary large exponent used in this
contradiction may depend on the polynomial itself.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialDyadic
open Polynomial
open scoped Classical

private theorem degree_le_of_pos_leading (f : Polynomial ℤ) (C K H : ℕ)
    (hl : 0 < f.leadingCoeff)
    (h : ∀ r, C ≤ r → (f.eval ((2 : ℤ) ^ r)).natAbs ≤ 2 ^ (K * r + H)) :
    f.natDegree ≤ K := by
  by_contra hn
  have hk : K < f.natDegree := by omega
  let q : Polynomial ℤ := Polynomial.C ((2 : ℤ) ^ H) * Polynomial.X ^ K
  let g := f - q
  have hq : q.degree < f.degree :=
    Polynomial.degree_lt_degree ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans_lt hk)
  have hgl : g.leadingCoeff = f.leadingCoeff := Polynomial.leadingCoeff_sub_of_degree_lt hq
  let r := C + (coefficientMass g + 1).size
  have hr : C ≤ r := by dsimp [r]; omega
  have hm : coefficientMass g + 1 ≤ 2 ^ r :=
    (Nat.lt_size_self (coefficientMass g + 1)).le.trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [r]; omega))
  have hs := IntegerPolynomialOuterSign.sign_after_mass g ((2 : ℝ) ^ r) (by exact_mod_cast hm)
  have hpositive : 0 < g.eval₂ (Int.castRingHom ℝ) ((2 : ℝ) ^ r) := by
    apply sign_eq_one_iff.mp
    apply hs.trans
    apply sign_eq_one_iff.mpr
    have hg : 0 < g.leadingCoeff := by rw [hgl]; exact hl
    exact_mod_cast hg
  have huInt : f.eval ((2 : ℤ) ^ r) ≤ ((2 ^ (K * r + H) : ℕ) : ℤ) :=
    Int.le_natAbs.trans (by exact_mod_cast h r hr)
  have hu : ((f.eval ((2 : ℤ) ^ r) : ℤ) : ℝ) ≤ (2 : ℝ) ^ (K * r + H) := by exact_mod_cast huInt
  have he : f.eval₂ (Int.castRingHom ℝ) ((2 : ℝ) ^ r) = ((f.eval ((2 : ℤ) ^ r) : ℤ) : ℝ) := by
    simpa only [map_pow, map_ofNat, Int.coe_castRingHom] using
      (Polynomial.eval₂_at_apply (p := f) (Int.castRingHom ℝ) ((2 : ℤ) ^ r))
  have hg : g.eval₂ (Int.castRingHom ℝ) ((2 : ℝ) ^ r) =
      f.eval₂ (Int.castRingHom ℝ) ((2 : ℝ) ^ r) - (2 : ℝ) ^ H * ((2 : ℝ) ^ r) ^ K := by
    simp only [g, q, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, map_pow, map_ofNat]
  have hp : (2 : ℝ) ^ (K * r + H) = (2 : ℝ) ^ H * ((2 : ℝ) ^ r) ^ K := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hg, he, ← hp] at hpositive
  linarith

theorem natDegree_le (f : Polynomial ℤ) (C K H : ℕ)
    (h : ∀ r, C ≤ r → (f.eval ((2 : ℤ) ^ r)).natAbs ≤ 2 ^ (K * r + H)) :
    f.natDegree ≤ K := by
  by_cases hf : f = 0
  · simp only [hf, Polynomial.natDegree_zero, Nat.zero_le]
  · have hl : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
    rcases lt_or_gt_of_ne hl with hn | hp
    · have hd := degree_le_of_pos_leading (-f) C K H (by simpa only [Polynomial.leadingCoeff_neg] using neg_pos.mpr hn)
        (fun r hr => by simpa only [Polynomial.eval_neg, Int.natAbs_neg] using h r hr)
      simpa only [Polynomial.natDegree_neg] using hd
    · exact degree_le_of_pos_leading f C K H hp h

end LeanCanny.Algebra.IntegerPolynomialDyadic
