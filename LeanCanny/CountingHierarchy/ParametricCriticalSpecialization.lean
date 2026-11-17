/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalPolynomial
public import LeanCanny.CountingHierarchy.PowerTraceCharacteristic
public import LeanCanny.CountingHierarchy.InitialCriticalSeparable

/-! # Specialization of the integer critical-value polynomial -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue
open scoped Classical

variable {n : ℕ}

/-- The integer parameter polynomial specializes to the actual critical
 quotient over a field, in characteristic zero or at sufficiently large primes. -/
theorem parametricCriticalValue_map {K : Type*} [Field K] (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (u : K)
    (hK : ∀ j, 1 ≤ j → j ≤ (d + 1) ^ n → (j : K) ≠ 0) :
    (parametricCriticalValue d F hF).map (parameterEvaluation u) =
      (multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : K)) u
          (F.map (Int.castRingHom K)))
        (criticalLower_degree (d + 1) (by omega) _ _ _
          ((map_degree_le (Int.castRingHom K) F).trans hF))
        (deformedPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : K)) u
          (F.map (Int.castRingHom K)))).charpoly := by
  have hr (i : Fin n) : (parameterLower d F i).totalDegree ≤ d := by
    have := parameterLower_degree d F hF i
    omega
  have h := multiplicationMatrix_charpoly_map (parameterEvaluation u) d hd
    (parameterLower d F) hr (parameterObjective d F) hK
  have hlow : (fun i : Fin n => (parameterLower d F i).map (parameterEvaluation u)) =
      criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : K)) u
        (F.map (Int.castRingHom K)) := funext (parameterLower_map d u F)
  exact h.trans (multiplicationMatrix_charpoly_congr (ell := d + 1) (by omega) _ _ _ _ _ _
    hlow (parameterObjective_map d u F))

/-- At parameter zero the characteristic polynomial is separable. This
 is a theorem about the reduction of the original integer polynomial. -/
theorem parametricCriticalValue_at_zero_separable (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) :
    ((parametricCriticalValue d F hF).map (parameterEvaluation (0 : ℂ))).Separable := by
  have hK : ∀ j : ℕ, 1 ≤ j → j ≤ (d + 1) ^ n → (j : ℂ) ≠ 0 := by
    intro j hj _
    exact_mod_cast (by omega : j ≠ 0)
  have hm := parametricCriticalValue_map d hd F hF (0 : ℂ) hK
  have hi := initial_critical_charpoly_separable (n := n) (d + 1) (by omega)
    _ (Complex.isPrimitiveRoot_exp (d + 1) (by omega))
  have he := multiplicationMatrix_charpoly_congr (n := n) (ell := d + 1) (by omega)
    (criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : ℂ)) 0
      (F.map (Int.castRingHom ℂ)))
    (fun i => MvPolynomial.C ((separatedCenters (d + 1) i : ℂ) ^ (d + 1)))
    (criticalLower_degree (d + 1) (by omega) _ _ _
      ((map_degree_le (Int.castRingHom ℂ) F).trans hF))
    (fun _ => by simpa only [totalDegree_C] using (show 0 < d + 1 by omega))
    (deformedPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : ℂ)) 0
      (F.map (Int.castRingHom ℂ))) (potentialPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : ℂ)))
    (by funext i; simp only [criticalLower, map_zero, zero_mul, sub_zero])
    (by simp only [deformedPolynomial, mul_zero, map_zero, zero_mul, add_zero])
  exact (hm.trans he).symm ▸ hi

end LeanCanny.CountingHierarchy
