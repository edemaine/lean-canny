/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCriticalSpecialization
public import LeanCanny.CountingHierarchy.CriticalMinimumValue
public import LeanCanny.CountingHierarchy.MonicPowerSubstitution

/-! # Actual relative critical polynomials vanish at the fiber minima -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial
open scoped Classical

variable {n : ℕ} {κ : Type*}

/-- Outer variable is the critical value, inner variable the penalty parameter. -/
noncomputable def relativeBivariate (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (x : κ → ℝ) : Polynomial (Polynomial ℝ) :=
  (LeanCanny.CountingHierarchy.relativeCharacteristic d F hF).map
    (relativeParameterEvaluation Polynomial.X (fun i => Polynomial.C (x i)))

theorem relativeBivariate_monic (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (x : κ → ℝ) : (relativeBivariate d F hF x).Monic :=
  (relativeCharacteristic_monic d F hF).map _

theorem relativeBivariate_natDegree (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (x : κ → ℝ) :
    (relativeBivariate d F hF x).natDegree = (d + 1) ^ n := by
  rw [relativeBivariate, (relativeCharacteristic_monic d F hF).natDegree_map,
    relativeCharacteristic_natDegree]

theorem relativeBivariate_map (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (x : κ → ℝ) (u : ℝ) :
    (relativeBivariate d F hF x).map (Polynomial.evalRingHom u) =
      (LeanCanny.CountingHierarchy.relativeCharacteristic d F hF).map (relativeParameterEvaluation u x) := by
  rw [relativeBivariate, Polynomial.map_map]
  congr 1
  ext a
  · simp [relativeParameterEvaluation]
  · cases a <;> simp [relativeParameterEvaluation]

theorem relativeBivariate_root_at_minimum (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ d + 1) (x : κ → ℝ)
    (hFn : ∀ z, 0 ≤ MvPolynomial.eval z (relativeSpecializedSource F x)) (u : ℝ) (hu : 0 ≤ u) :
    (relativeBivariate d F hF x).eval₂ (Polynomial.evalRingHom u)
      (criticalMinimumValue (d + 1) (fun _ => 0) (relativeSpecializedSource F x) u) = 0 := by
  rw [← Polynomial.eval_map, relativeBivariate_map,
    relativeCharacteristic_map d hd F hF u x (by
      intro j hj _
      exact_mod_cast (by omega : j ≠ 0))]
  exact characteristic_root_at_criticalMinimumValue (d + 1) (by omega) he (fun _ => 0)
    (fun _ => le_rfl) (relativeSpecializedSource F x)
    ((relativeSpecializedSource_degree F x).trans hF) hFn u hu

theorem relativePowerSection_ne_zero (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (x : κ → ℝ) :
    monicPowerSubstitution ((d + 1) ^ n) (relativeBivariate d F hF x) ≠ 0 :=
  monicPowerSubstitution_ne_zero _ _ (relativeBivariate_monic d F hF x)
    (relativeBivariate_natDegree d F hF x)

end LeanCanny.CountingHierarchy
