/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RootLabelScore
public import LeanCanny.CountingHierarchy.RationalSignProductBounds

/-! # Clearing the positive denominators of sign approximants -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

@[expose] noncomputable def signTestDenominator (B s : ℕ) (g : Polynomial ℤ) : Polynomial ℤ :=
  (rationalSignProduct B s).comp g + (rationalSignProduct B s).comp (-g)

@[expose] noncomputable def signTestNumerator (B s : ℕ) (g : Polynomial ℤ) : Polynomial ℤ :=
  (rationalSignProduct B s).comp g - (rationalSignProduct B s).comp (-g)

@[expose] noncomputable def signTestCommonDenominator {m : ℕ}
    (B s : ℕ) (g : Fin m → Polynomial ℤ) : Polynomial ℤ :=
  ∏ i, signTestDenominator B s (g i)

@[expose] noncomputable def signTestClearedNumerator {m : ℕ}
    (B s : ℕ) (g : Fin m → Polynomial ℤ) (i : Fin m) : Polynomial ℤ :=
  signTestNumerator B s (g i) * ∏ j ∈ Finset.univ.erase i, signTestDenominator B s (g j)

theorem signTestDenominator_eval (B s : ℕ) (g : Polynomial ℤ) (x : ℝ) :
    (signTestDenominator B s g).eval₂ (Int.castRingHom ℝ) x =
      signProductValue B s (g.eval₂ (Int.castRingHom ℝ) x) +
        signProductValue B s (-g.eval₂ (Int.castRingHom ℝ) x) := by
  simp only [signTestDenominator, Polynomial.eval₂_add, Polynomial.eval₂_comp,
    Polynomial.eval₂_neg, signProductValue]

theorem signTestNumerator_eval (B s : ℕ) (g : Polynomial ℤ) (x : ℝ) :
    (signTestNumerator B s g).eval₂ (Int.castRingHom ℝ) x =
      signProductValue B s (g.eval₂ (Int.castRingHom ℝ) x) -
        signProductValue B s (-g.eval₂ (Int.castRingHom ℝ) x) := by
  simp only [signTestNumerator, Polynomial.eval₂_sub, Polynomial.eval₂_comp,
    Polynomial.eval₂_neg, signProductValue]

theorem signTestDenominator_eval_ge_one (B s : ℕ) (g : Polynomial ℤ) (x : ℝ) :
    1 ≤ (signTestDenominator B s g).eval₂ (Int.castRingHom ℝ) x := by
  rw [signTestDenominator_eval]
  exact signProduct_denominator_ge_one B s _

theorem signTestCommonDenominator_eval_ge_one {m : ℕ}
    (B s : ℕ) (g : Fin m → Polynomial ℤ) (x : ℝ) :
    1 ≤ (signTestCommonDenominator B s g).eval₂ (Int.castRingHom ℝ) x := by
  rw [signTestCommonDenominator, Polynomial.eval₂_finsetProd]
  exact Finset.one_le_prod₀ (fun i _ => signTestDenominator_eval_ge_one B s (g i) x)

/-- The explicit product omitting one denominator equals the common
 denominator times the corresponding rational approximation. -/
theorem signTestClearedNumerator_eval {m : ℕ} (B s : ℕ)
    (g : Fin m → Polynomial ℤ) (i : Fin m) (x : ℝ) :
    (signTestClearedNumerator B s g i).eval₂ (Int.castRingHom ℝ) x =
      (signTestCommonDenominator B s g).eval₂ (Int.castRingHom ℝ) x *
        rationalSignApproximation B s ((g i).eval₂ (Int.castRingHom ℝ) x) := by
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) x
  have hd : φ (signTestDenominator B s (g i)) ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (signTestDenominator_eval_ge_one B s (g i) x))
  have he : φ (signTestCommonDenominator B s g) =
      φ (signTestDenominator B s (g i)) * ∏ j ∈ Finset.univ.erase i, φ (signTestDenominator B s (g j)) := by
    rw [signTestCommonDenominator, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have ha : rationalSignApproximation B s ((g i).eval₂ (Int.castRingHom ℝ) x) =
      φ (signTestNumerator B s (g i)) / φ (signTestDenominator B s (g i)) := by
    rw [show φ (signTestNumerator B s (g i)) = _ from signTestNumerator_eval B s (g i) x,
      show φ (signTestDenominator B s (g i)) = _ from signTestDenominator_eval B s (g i) x]
    rfl
  change φ (signTestClearedNumerator B s g i) = φ (signTestCommonDenominator B s g) * _
  rw [signTestClearedNumerator, map_mul, map_prod, he, ha]
  field_simp [hd]

end LeanCanny.CountingHierarchy
