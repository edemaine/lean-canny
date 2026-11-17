/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalDiscriminant
public import LeanCanny.CountingHierarchy.IntegerAlgebraicThreshold
public import LeanCanny.CountingHierarchy.CriticalMinimumValue
public import LeanCanny.CountingHierarchy.QuotientSimpleRoot

/-! # A single critical-value specialization detects real feasibility -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial PurePowerResidue Set
open scoped Classical

variable {n : ℕ}

@[expose] noncomputable def integerCriticalMinimum (d : ℕ)
    (F : MvPolynomial (Fin n) ℤ) : ℝ → ℝ :=
  criticalMinimumValue (d + 1) (fun i => (separatedCenters (d + 1) i : ℝ))
    (F.map (Int.castRingHom ℝ))

theorem parametricCriticalValue_root_at_minimum (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ)))
    (u : ℝ) (hu : 0 ≤ u) :
    ((parametricCriticalValue d F hF).map (parameterEvaluation u)).eval
      (integerCriticalMinimum d F u) = 0 := by
  rw [parametricCriticalValue_map d hd F hF u (by
    intro j hj _
    exact_mod_cast (by omega : j ≠ 0))]
  exact characteristic_root_at_criticalMinimumValue (d + 1) (by omega) he _
    (fun _ => Nat.cast_nonneg _) _ ((PurePowerResidue.map_degree_le _ F).trans hF) hFn u hu

/-- The minimum branch satisfies the integer bivariate equation viewed
 as a polynomial in the deformation parameter. -/
theorem swappedCriticalValue_root_at_minimum (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ)))
    (u : ℝ) (hu : 0 ≤ u) :
    (Bivariate.swap (parametricCriticalValue d F hF)).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (integerCriticalMinimum d F u)) u = 0 := by
  rw [integer_bivariate_swap_eval]
  simpa only [Polynomial.eval_map, parameterEvaluation] using
    parametricCriticalValue_root_at_minimum d hd he F hF hFn u hu

/-- Every real root after a discriminant-avoiding specialization is
 realized at an actual real point of the critical equations. -/
theorem exists_real_critical_point_of_specialized_root (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (u η : ℝ)
    (hu : (LeanCanny.Algebra.coefficientMass (criticalDiscriminant d F hF) : ℝ) + 1 ≤ |u|)
    (hroot : ((parametricCriticalValue d F hF).map (parameterEvaluation u)).IsRoot η) :
    ∃ x : Fin n → ℝ,
      (∀ i, MvPolynomial.aeval x
        (criticalLower (d + 1) (fun j => (separatedCenters (d + 1) j : ℝ)) u
          (F.map (Int.castRingHom ℝ)) i) = x i ^ (d + 1)) ∧
      criticalObjective (d + 1) (fun j => (separatedCenters (d + 1) j : ℝ))
        (F.map (Int.castRingHom ℝ)) u x = η := by
  have hs := criticalValue_separable_of_large_parameter d hd F hF u hu
  have hq := parametricCriticalValue_map d hd F hF u (by
    intro j hj _
    exact_mod_cast (by omega : j ≠ 0))
  rw [hq] at hroot hs
  have hm : _root_.Polynomial.rootMultiplicity η
      ((multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : ℝ)) u
          (F.map (Int.castRingHom ℝ)))
        (criticalLower_degree (d + 1) (by omega) _ _ _
          ((PurePowerResidue.map_degree_le _ F).trans hF))
        (deformedPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : ℝ)) u
          (F.map (Int.castRingHom ℝ)))).charpoly) = 1 := by
    apply Nat.le_antisymm (Polynomial.rootMultiplicity_le_one_of_separable hs η)
    exact Nat.succ_le_iff.mpr ((Polynomial.rootMultiplicity_pos
      (Matrix.charpoly_monic _).ne_zero).mpr hroot)
  obtain ⟨x, hx, hv⟩ := exists_common_zero_of_simple_charpoly_root (by omega : 1 ≤ d + 1)
    _ _ _ η hroot hm
  refine ⟨x, hx, ?_⟩
  rw [criticalObjective_eq_eval]
  simpa only [MvPolynomial.aeval_eq_eval] using hv

end LeanCanny.CountingHierarchy
