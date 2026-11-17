/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCriticalPolynomial
public import LeanCanny.CountingHierarchy.CriticalPolynomialMap
public import LeanCanny.CountingHierarchy.PowerTraceCharacteristic

/-! # Specializing a critical polynomial with retained parameters -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue
open scoped Classical

variable {n : ℕ} {κ K : Type*}

section Ring

variable [CommRing K]

noncomputable def relativeParameterEvaluation (u : K) (x : κ → K) :
    MvPolynomial (Option κ) ℤ →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i => i.elim u x)

noncomputable def relativeSpecializedSource (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (x : κ → K) : MvPolynomial (Fin n) K :=
  (splitIntegerPolynomial F).map (MvPolynomial.eval₂Hom (Int.castRingHom K) x)

theorem relativeSource_map (F : MvPolynomial (Fin n ⊕ κ) ℤ) (u : K) (x : κ → K) :
    (relativeSource F).map (relativeParameterEvaluation u x) = relativeSpecializedSource F x := by
  rw [relativeSource, MvPolynomial.map_map]
  congr 1
  ext a i <;> simp [relativeParameterEvaluation]

theorem relativeSpecializedSource_degree (F : MvPolynomial (Fin n ⊕ κ) ℤ) (x : κ → K) :
    (relativeSpecializedSource F x).totalDegree ≤ F.totalDegree :=
  (map_degree_le _ _).trans (splitIntegerPolynomial_mainDegree_le F)

theorem relativeLower_map (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ) (u : K)
    (x : κ → K) (i : Fin n) :
    (relativeLower d F i).map (relativeParameterEvaluation u x) =
      criticalLower (d + 1) (fun _ => 0) u (relativeSpecializedSource F x) i := by
  rw [relativeLower, criticalLower_map, relativeSource_map]
  simp only [map_zero, relativeParameterEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, Option.elim_none]

theorem relativeObjective_map (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ) (u : K)
    (x : κ → K) :
    (relativeObjective d F).map (relativeParameterEvaluation u x) =
      deformedPolynomial (d + 1) (fun _ => 0) u (relativeSpecializedSource F x) := by
  rw [relativeObjective, deformedPolynomial_map, relativeSource_map]
  simp only [map_zero, relativeParameterEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, Option.elim_none]

end Ring

section Field

variable [Field K]

theorem relativeCharacteristic_map (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ d + 1) (u : K) (x : κ → K)
    (hK : ∀ j, 1 ≤ j → j ≤ (d + 1) ^ n → (j : K) ≠ 0) :
    (relativeCharacteristic d F hF).map (relativeParameterEvaluation u x) =
      (multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun _ => 0) u (relativeSpecializedSource F x))
        (criticalLower_degree (d + 1) (by omega) _ _ _
          ((relativeSpecializedSource_degree F x).trans hF))
        (deformedPolynomial (d + 1) (fun _ => 0) u (relativeSpecializedSource F x))).charpoly := by
  have hr (i : Fin n) : (relativeLower d F i).totalDegree ≤ d := by
    have := relativeLower_mainDegree d F hF i
    omega
  have h := multiplicationMatrix_charpoly_map (relativeParameterEvaluation u x) d hd
    (relativeLower d F) hr (relativeObjective d F) hK
  exact h.trans (multiplicationMatrix_charpoly_congr (ell := d + 1) (by omega) _ _ _ _ _ _
    (funext (relativeLower_map d F u x)) (relativeObjective_map d F u x))

end Field

end LeanCanny.CountingHierarchy
