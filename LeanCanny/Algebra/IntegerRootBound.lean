/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientBounds
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Basic.Real.Basic

/-! # A coefficient-mass bound on real roots of integer polynomials -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra
open Polynomial

theorem abs_root_lt_coefficientMass_add_one (p : ℤ[X]) (hp : p ≠ 0) (a : ℝ)
    (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) :
    |a| < (coefficientMass p : ℝ) + 1 := by
  let q := p.map (Int.castRingHom ℝ)
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hcoeff (i : ℕ) : ‖q.coeff i‖₊ ≤ (coefficientMass p : NNReal) := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_natCast, coe_nnnorm, Real.norm_eq_abs, q, coeff_map,
      Int.coe_castRingHom, ← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast coeff_natAbs_le_coefficientMass p i
  have hlc : (1 : NNReal) ≤ ‖q.leadingCoeff‖₊ := by
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs]
    have he : q.leadingCoeff = (p.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj p
    rw [he, ← Int.cast_abs]
    have h : (1 : ℤ) ≤ |p.leadingCoeff| := by
      have := abs_pos.mpr (leadingCoeff_ne_zero.mpr hp)
      omega
    simpa only [Int.cast_one, NNReal.coe_one] using ((Int.cast_le (R := ℝ)).mpr h)
  have hb : q.cauchyBound ≤ (coefficientMass p : NNReal) + 1 := by
    unfold cauchyBound
    gcongr
    exact (div_le_self (by positivity) hlc).trans (Finset.sup_le fun i _ => hcoeff i)
  have hr : ‖a‖₊ < q.cauchyBound := IsRoot.norm_lt_cauchyBound hq (by simpa only [IsRoot, q, eval_map] using ha)
  have ht := hr.trans_le hb
  exact_mod_cast ht

end LeanCanny.Algebra
