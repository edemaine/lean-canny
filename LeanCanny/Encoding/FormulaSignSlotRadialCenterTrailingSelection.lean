/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSquarefreeSelection
/-! # Finite same-center guards for the actual trailing target coefficient

Zero tests retain the entire radius polynomial. This selects the literal
margin trailing coefficient without specializing the radius or copying a
symbolic trailing index through the center map.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterTrailingSelection
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem coordinate_eq (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D : ℕ)
    (h : FormulaSignSlotRadialCenterSelection.Guards c a tau D) :
    FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a =
      (FormulaSignSlotRadialCenterSelection.specialized c a).coeff tau :=
  (FormulaSignSlotRadialCenterSelection.coordinate_at c a tau D h).trans
    (FormulaSignSlotRadialFormalEliminant.coefficient_specialization _ _ _ _).symm

theorem radius_zero_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D j : ℕ)
    (h : FormulaSignSlotRadialCenterSelection.Guards c a tau D) :
    (∀ r < FormulaSignSlotRadialCenterSelection.bound c + 1,
      FormulaSignSlotRadialCenterSelection.Zero c a tau j r) ↔
        (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).coeff j = 0 := by
  rw [coordinate_eq c a tau D h]
  exact FormulaSignSlotRadialCenterSelection.radius_zero_iff c a tau j

noncomputable def Guards (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D ell : ℕ) : Prop :=
  FormulaSignSlotRadialCenterSelection.Guards c a tau D ∧ ell ≤ D ∧
    (∀ j < ell, ∀ r < FormulaSignSlotRadialCenterSelection.bound c + 1,
      FormulaSignSlotRadialCenterSelection.Zero c a tau j r) ∧
    ¬∀ r < FormulaSignSlotRadialCenterSelection.bound c + 1,
      FormulaSignSlotRadialCenterSelection.Zero c a tau ell r

theorem guards_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D ell : ℕ) :
    Guards c a tau D ell ↔ FormulaSignSlotRadialCenterSelection.Guards c a tau D ∧
      ell = (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).natTrailingDegree := by
  have HN : FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a ≠ 0 :=
    FormulaSignSlotRadialParameterEliminant.coordinate_ne_zero _ _ _
  constructor
  · rintro ⟨HS, _, HL, HC⟩
    refine ⟨HS, Nat.le_antisymm ?_ ?_⟩
    · by_contra H
      have HZ := (radius_zero_iff c a tau D
        (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).natTrailingDegree HS).mp
          (HL _ (by omega))
      exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr HN) HZ
    · exact Polynomial.natTrailingDegree_le_of_ne_zero ((radius_zero_iff c a tau D ell HS).not.mp HC)
  · rintro ⟨HS, rfl⟩
    refine ⟨HS, (Polynomial.natTrailingDegree_le_natDegree _).trans
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree c a tau D HS).le, ?_, ?_⟩
    · intro j hj
      exact (radius_zero_iff c a tau D j HS).mpr (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj)
    · exact (radius_zero_iff c a tau D _ HS).not.mpr
        (Polynomial.coeff_natTrailingDegree_ne_zero.mpr HN)

theorem coefficient (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D ell r : ℕ)
    (h : Guards c a tau D ell) :
    (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff.coeff r =
      (FormulaSignSlotRadialCenterCoefficient.polynomial c tau ell r).eval₂ (Int.castRingHom ℝ) a := by
  have HE := (guards_iff c a tau D ell).mp h |>.2
  rw [Polynomial.trailingCoeff, ← HE, coordinate_eq c a tau D h.1]
  exact FormulaSignSlotRadialCenterSelection.coefficient c a tau ell r

theorem exists_guards (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) :
    ∃ tau ≤ FormulaSignSlotRadialCenterSelection.bound c,
      ∃ D ≤ FormulaSignSlotRadialCenterSelection.bound c,
        ∃ ell ≤ D, Guards c a tau D ell := by
  obtain ⟨tau, ht, D, hD, HS⟩ := FormulaSignSlotRadialCenterSelection.exists_guards c a
  have HL := Polynomial.natTrailingDegree_le_natDegree
    (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a)
  rw [FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree c a tau D HS] at HL
  exact ⟨tau, ht, D, hD, _, HL, (guards_iff c a tau D _).mpr ⟨HS, rfl⟩⟩

end LeanCanny.Encoding.FormulaSignSlotRadialCenterTrailingSelection
