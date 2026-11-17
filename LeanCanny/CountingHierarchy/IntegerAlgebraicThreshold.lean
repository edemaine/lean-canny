/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.AlgebraicMinimumThreshold
public import LeanCanny.CountingHierarchy.IntegerBivariate

/-! # One large specialization detects bounded algebraic branches -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Set

@[expose] noncomputable def integerValueSection (P : Polynomial (Polynomial ℤ)) (R : ℤ) :
    Polynomial ℤ := P.map (Polynomial.evalRingHom R)

theorem integerValueSection_eval (P : Polynomial (Polynomial ℤ)) (R : ℤ) (u : ℝ) :
    (integerValueSection P R).eval₂ (Int.castRingHom ℝ) u =
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (R : ℝ)) u := by
  rw [integerValueSection, Polynomial.eval₂_map]
  congr 1
  ext <;> simp

/-- A sufficiently large integer value cannot annihilate the leading
 coefficient, so the resulting parameter polynomial remains nonzero. -/
theorem integerValueSection_ne_zero (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0)
    (R : ℤ) (hR : (LeanCanny.Algebra.coefficientMass P.leadingCoeff : ℝ) + 1 ≤ (R : ℝ)) :
    integerValueSection P R ≠ 0 := by
  intro hz
  have he := congrArg (fun p : Polynomial ℤ => p.coeff P.natDegree) hz
  have hl : P.leadingCoeff.eval R = 0 := by
    simpa only [integerValueSection, coeff_map, coeff_zero, Polynomial.leadingCoeff,
      Polynomial.coe_evalRingHom] using he
  have hc : P.leadingCoeff.eval₂ (Int.castRingHom ℝ) (R : ℝ) = 0 := by
    change P.leadingCoeff.eval₂ (Int.castRingHom ℝ) ((Int.castRingHom ℝ) R) = 0
    rw [Polynomial.eval₂_at_apply, hl, map_zero]
  have hb := LeanCanny.Algebra.abs_root_lt_coefficientMass_add_one P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP) (R : ℝ) hc
  have hpos : (0 : ℝ) ≤ R :=
    (by positivity : (0 : ℝ) ≤ (LeanCanny.Algebra.coefficientMass P.leadingCoeff : ℝ) + 1).trans hR
  rw [abs_of_nonneg hpos] at hb
  exact (not_lt_of_ge hR) hb

theorem integerValueSection_eval_ne_zero (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0)
    (R : ℤ) (hR : (LeanCanny.Algebra.coefficientMass P.leadingCoeff : ℝ) + 1 ≤ (R : ℝ))
    (u : ℝ) (hu : (LeanCanny.Algebra.coefficientMass (integerValueSection P R) : ℝ) + 1 ≤ u) :
    P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (R : ℝ)) u ≠ 0 := by
  rw [← integerValueSection_eval]
  intro hz
  have hb := LeanCanny.Algebra.abs_root_lt_coefficientMass_add_one
    (integerValueSection P R) (integerValueSection_ne_zero P hP R hR) u hz
  have hpos : 0 ≤ u :=
    (by positivity : (0 : ℝ) ≤ (LeanCanny.Algebra.coefficientMass (integerValueSection P R) : ℝ) + 1).trans hu
  rw [abs_of_nonneg hpos] at hb
  exact (not_lt_of_ge hu) hb

/-- The boundedness question for a continuous nondecreasing algebraic root
 branch reduces to its value at one explicitly bounded real parameter. -/
theorem bounded_branch_iff_at_large_parameter (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0)
    (m : ℝ → ℝ) (hm : MonotoneOn m (Ici 0)) (hc : ContinuousOn m (Ici 0))
    (hroot : ∀ u : ℝ, 0 < u →
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u = 0)
    (R : ℤ) (hR : (LeanCanny.Algebra.coefficientMass P.leadingCoeff : ℝ) + 1 ≤ (R : ℝ))
    (U : ℝ) (hU : (LeanCanny.Algebra.coefficientMass (integerValueSection P R) : ℝ) + 1 ≤ U) :
    (∃ B, ∀ u, 0 ≤ u → m u ≤ B) ↔ m U < R := by
  have hpos : 0 < U := lt_of_lt_of_le (by positivity) hU
  constructor
  · intro hb
    exact bounded_branch_lt_threshold P hP m hm hroot (R : ℝ) hR hb U hpos.le
  · intro hstart
    refine ⟨(R : ℝ), bounded_of_no_threshold_crossing m hm hc U (R : ℝ) hpos.le hstart ?_⟩
    intro u hu he
    have hzero := hroot u (hpos.trans_le hu)
    rw [he] at hzero
    exact integerValueSection_eval_ne_zero P hP R hR u (hU.trans hu) hzero

end LeanCanny.CountingHierarchy
