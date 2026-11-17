/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalMinimum

/-! # Bounded critical-value minima detect real zeros -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Set PurePowerResidue
open scoped Classical Topology

variable {n : ℕ}

@[expose] noncomputable def criticalMinimumValue (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) : ℝ :=
  coerciveMinimumValue (fun x => (ell + 1 : ℕ) * eval x F) (separatedPotential ell a) u

theorem criticalMinimumValue_eq (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) (x : Fin n → ℝ)
    (hx : IsMinOn (criticalObjective ell a F u) univ x) :
    criticalMinimumValue ell a F u = criticalObjective ell a F u x :=
  coerciveMinimumValue_eq_of_minimizer _ _ u x hx

theorem criticalMinimumValue_continuousOn (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hFn : ∀ x, 0 ≤ eval x F) :
    ContinuousOn (criticalMinimumValue ell a F) (Ici 0) := by
  apply coerciveMinimumValue_continuousOn
    (fun x => (ell + 1 : ℕ) * eval x F) (separatedPotential ell a)
    (continuous_const.mul (MvPolynomial.continuous_eval F))
    (continuous_separatedPotential ell a) (fun x => mul_nonneg (by positivity) (hFn x))
    (separatedPotential_compact_sublevel ell hell he a ha) (fun _ => 0)

theorem criticalMinimumValue_monotoneOn (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hFn : ∀ x, 0 ≤ eval x F) :
    MonotoneOn (criticalMinimumValue ell a F) (Ici 0) := by
  apply coerciveMinimumValue_monotoneOn
    (fun x => (ell + 1 : ℕ) * eval x F) (separatedPotential ell a)
    (continuous_const.mul (MvPolynomial.continuous_eval F))
    (continuous_separatedPotential ell a) (fun x => mul_nonneg (by positivity) (hFn x))
    (separatedPotential_compact_sublevel ell hell he a ha) (fun _ => 0)

theorem real_zero_iff_bounded_criticalMinimumValue (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hFn : ∀ x, 0 ≤ eval x F) :
    (∃ x : Fin n → ℝ, eval x F = 0) ↔
      ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → criticalMinimumValue ell a F u ≤ B := by
  have hm : ((ell + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ell
  simpa only [criticalMinimumValue, mul_eq_zero, hm, false_or] using
    zero_iff_bounded_minimumValue
      (fun x => (ell + 1 : ℕ) * eval x F) (separatedPotential ell a)
      (continuous_const.mul (MvPolynomial.continuous_eval F))
      (continuous_separatedPotential ell a) (fun x => mul_nonneg (by positivity) (hFn x))
      (separatedPotential_nonneg ell he a ha)
      (separatedPotential_compact_sublevel ell hell he a ha) (fun _ => 0)

theorem characteristic_root_at_criticalMinimumValue (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : F.totalDegree ≤ ell) (hFn : ∀ x, 0 ≤ eval x F)
    (u : ℝ) (hu : 0 ≤ u) :
    ((multiplicationMatrix hell (criticalLower ell a u F)
      (criticalLower_degree ell hell a u F hF) (deformedPolynomial ell a u F)).charpoly).eval
        (criticalMinimumValue ell a F u) = 0 := by
  obtain ⟨x, hx⟩ := exists_critical_minimizer ell hell he a ha F hFn u hu
  rw [criticalMinimumValue_eq ell a F u x hx]
  exact characteristic_root_of_minimizer ell hell a F hF u x hx

end LeanCanny.CountingHierarchy
