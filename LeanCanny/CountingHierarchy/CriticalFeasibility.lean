/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalValueSpecialization

/-! # Real feasibility is a root test at one finite specialization

The cutoff hypotheses are explicit integer coefficient masses. Bounding and
computing suitable short exponents for controlled families is a separate step.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial PurePowerResidue Set
open scoped Classical

variable {n : ℕ}

/-- A nonnegative integer polynomial has a real zero exactly when the
 explicitly constructed specialized characteristic polynomial has a real
 root below the value cutoff. No characteristic polynomial or critical-point
 oracle is assumed. -/
theorem real_zero_iff_specialized_critical_root (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ)))
    (R : ℤ)
    (hR : (LeanCanny.Algebra.coefficientMass
      (Bivariate.swap (parametricCriticalValue d F hF)).leadingCoeff : ℝ) + 1 ≤ (R : ℝ))
    (U : ℝ)
    (hU : (LeanCanny.Algebra.coefficientMass
      (integerValueSection (Bivariate.swap (parametricCriticalValue d F hF)) R) : ℝ) + 1 ≤ U)
    (hδ : (LeanCanny.Algebra.coefficientMass (criticalDiscriminant d F hF) : ℝ) + 1 ≤ U) :
    (∃ x : Fin n → ℝ, MvPolynomial.eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ η : ℝ, η < R ∧
        ((parametricCriticalValue d F hF).map (parameterEvaluation U)).IsRoot η := by
  let a : Fin n → ℝ := fun i => (separatedCenters (d + 1) i : ℝ)
  let Fℝ := F.map (Int.castRingHom ℝ)
  let m := integerCriticalMinimum d F
  let P := Bivariate.swap (parametricCriticalValue d F hF)
  have hP : P ≠ 0 := by
    intro hz
    have h := congrArg Bivariate.swap hz
    have hq : parametricCriticalValue d F hF = 0 := by
      simpa only [P, Bivariate.swap_swap_apply, map_zero] using h
    exact (parametricCriticalValue_monic d F hF).ne_zero hq
  have ha (i : Fin n) : 0 ≤ a i := Nat.cast_nonneg _
  have hm : MonotoneOn m (Ici 0) :=
    criticalMinimumValue_monotoneOn (d + 1) (by omega) he a ha Fℝ hFn
  have hc : ContinuousOn m (Ici 0) :=
    criticalMinimumValue_continuousOn (d + 1) (by omega) he a ha Fℝ hFn
  have hr (u : ℝ) (hu : 0 < u) :
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u = 0 :=
    swappedCriticalValue_root_at_minimum d hd he F hF hFn u hu.le
  have hb := bounded_branch_iff_at_large_parameter P hP m hm hc hr R hR U hU
  have hz := real_zero_iff_bounded_criticalMinimumValue (d + 1) (by omega) he a ha Fℝ hFn
  have hpos : 0 ≤ U :=
    (by positivity : (0 : ℝ) ≤ (LeanCanny.Algebra.coefficientMass
      (integerValueSection P R) : ℝ) + 1).trans hU
  constructor
  · intro hx
    refine ⟨m U, hb.mp (hz.mp hx), ?_⟩
    exact parametricCriticalValue_root_at_minimum d hd he F hF hFn U hpos
  · rintro ⟨η, hη, hroot⟩
    obtain ⟨x, _hx, hv⟩ := exists_real_critical_point_of_specialized_root d hd F hF U η
      (by simpa only [abs_of_nonneg hpos] using hδ) hroot
    obtain ⟨x₀, hx₀⟩ := exists_critical_minimizer (d + 1) (by omega) he a ha Fℝ hFn U hpos
    have hle : m U ≤ η := by
      change criticalMinimumValue (d + 1) a Fℝ U ≤ η
      rw [criticalMinimumValue_eq (d + 1) a Fℝ U x₀ hx₀]
      exact (hx₀ (mem_univ x)).trans_eq hv
    exact hz.mpr (hb.mpr (hle.trans_lt hη))

end LeanCanny.CountingHierarchy
