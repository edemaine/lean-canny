/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecificLimits.Basic
public import LeanCanny.Algebra.IntegerRootBound

/-! # Finite limits of algebraic root branches

A finite limit of a root branch is a root of the leading coefficient when
viewing the defining bivariate polynomial as a polynomial in the parameter.
Reversing that parameter makes the assertion an ordinary continuity argument.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter
open scoped Topology

/-- Joint continuity of evaluating both variables, including integer coefficients. -/
theorem continuous_bivariate_integer_eval (P : Polynomial (Polynomial ℤ)) :
    Continuous (fun z : ℝ × ℝ =>
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) z.1) z.2) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply continuous_finsetSum
  intro i _
  exact ((P.coeff i).continuous_eval₂ (Int.castRingHom ℝ)).comp continuous_fst |>.mul
    (continuous_snd.pow i)

/-- A branch converging to a finite value at positive infinity forces the
 leading coefficient in the parameter to vanish at that value. -/
theorem leadingCoefficient_root_of_branch_limit (P : Polynomial (Polynomial ℤ))
    (m : ℝ → ℝ) (L : ℝ) (hm : Tendsto m atTop (𝓝 L))
    (hroot : ∀ u : ℝ, 0 < u →
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u = 0) :
    P.leadingCoeff.eval₂ (Int.castRingHom ℝ) L = 0 := by
  have ht : Tendsto (fun u : ℝ => (m u, u⁻¹)) atTop (𝓝 (L, 0)) :=
    hm.prodMk_nhds tendsto_inv_atTop_zero
  have hc := (continuous_bivariate_integer_eval P.reverse).continuousAt.tendsto.comp ht
  have hz : ∀ᶠ u : ℝ in atTop,
      P.reverse.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u⁻¹ = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    let := invertibleOfNonzero (ne_of_gt hu)
    simpa only [invOf_eq_inv] using
      (Polynomial.eval₂_reverse_eq_zero_iff
        (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u P).mpr (hroot u hu)
  have he := tendsto_nhds_unique hc (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))
  simpa only [Polynomial.eval₂_at_zero, Polynomial.coeff_zero_reverse,
    Polynomial.coe_eval₂RingHom] using he

/-- The finite limit is bounded solely by the integer coefficient mass of
 the leading coefficient polynomial, independent of the branch. -/
theorem abs_branch_limit_lt (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0)
    (m : ℝ → ℝ) (L : ℝ) (hm : Tendsto m atTop (𝓝 L))
    (hroot : ∀ u : ℝ, 0 < u →
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u = 0) :
    |L| < (LeanCanny.Algebra.coefficientMass P.leadingCoeff : ℝ) + 1 :=
  LeanCanny.Algebra.abs_root_lt_coefficientMass_add_one P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP) L
    (leadingCoefficient_root_of_branch_limit P m L hm hroot)

end LeanCanny.CountingHierarchy
