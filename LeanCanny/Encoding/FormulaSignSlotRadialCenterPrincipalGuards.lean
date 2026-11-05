/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalCoefficient
/-! # Finite same-center integer coefficient tests select the actual GCD index -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalGuards
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotRadialCenterPrincipalFamily
open scoped Classical

noncomputable def Zero (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j r : ℕ) : Prop :=
  (FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial c j r).eval₂ (Int.castRingHom ℝ) a = 0

theorem radius_zero_iff (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j : ℕ)
    (hj : j < degree c) : (∀ r < degreeBound c + 1, Zero c a j r) ↔
      (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst (original c)) a)
        (FormulaSignSlotRadialCenterSquarefreeSelection.principal (original c) (tau c) (degree c) j) = 0 :=
  (FormulaSignSlotRadialCenterPrincipalCoefficient.zero_iff c a j).trans
    (FormulaSignSlotRadialCenterPrincipalCoefficient.unsigned_zero_iff c a j hj)

noncomputable def Guards (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (k : ℕ) : Prop :=
  FormulaSignSlotRadialCenterSelection.Guards (original c) a (tau c) (degree c) ∧
    if degree c = 0 then k = 0 else k < degree c ∧
      (∀ j < k, ∀ r < degreeBound c + 1, Zero c a j r) ∧
      ¬∀ r < degreeBound c + 1, Zero c a k r

theorem guards_iff (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (k : ℕ) :
    Guards c a k ↔ FormulaSignSlotRadialCenterSquarefreeSelection.Guards (original c) a (tau c) (degree c) k := by
  constructor
  · rintro ⟨HS, HK⟩
    refine ⟨HS, ?_⟩
    by_cases hD : degree c = 0
    · simpa only [hD, ite_true] using HK
    · rw [ite_eq_right hD] at HK ⊢
      exact ⟨HK.1, fun j hj => (radius_zero_iff c a j (lt_trans hj HK.1)).mp (HK.2.1 j hj),
        (radius_zero_iff c a k HK.1).not.mp HK.2.2⟩
  · rintro ⟨HS, HK⟩
    refine ⟨HS, ?_⟩
    by_cases hD : degree c = 0
    · simpa only [hD, ite_true] using HK
    · rw [ite_eq_right hD] at HK ⊢
      exact ⟨HK.1, fun j hj => (radius_zero_iff c a j (lt_trans hj HK.1)).mpr (HK.2.1 j hj),
        (radius_zero_iff c a k HK.1).not.mpr HK.2.2⟩

theorem index_iff (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (k : ℕ) :
    Guards c a k ↔ FormulaSignSlotRadialCenterSelection.Guards (original c) a (tau c) (degree c) ∧
      k = DomainSquarefree.index (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (original c) a) :=
  (guards_iff c a k).trans (FormulaSignSlotRadialCenterSquarefreeSelection.guards_iff _ _ _ _ _)

theorem exists_guards (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ)
    (HS : FormulaSignSlotRadialCenterSelection.Guards (original c) a (tau c) (degree c)) :
    ∃ k ≤ degree c, Guards c a k := by
  let p := FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (original c) a
  have HD := FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree (original c) a (tau c) (degree c) HS
  refine ⟨DomainSquarefree.index p, ?_, (index_iff c a _).mpr ⟨HS, rfl⟩⟩
  by_cases hD : degree c = 0
  · simp only [DomainSquarefree.index, p, HD, hD, dite_true]
    rfl
  · exact (DomainSquarefree.valid_fraction p (by change (p).natDegree ≠ 0; dsimp only [p]; omega)).index_lt.le.trans HD.le

end LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalGuards
