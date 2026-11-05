/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficient
/-! # Finite same-center guards select the actual radial coordinate equation

All polynomial zero tests retain the same center. Lower perturbation
coefficients, the surviving target leading coefficient and higher target
coefficients are checked against one original-only finite bound.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterSelection
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterEliminant.eliminant

noncomputable abbrev bound := FormulaSignSlotRadialEliminantPacked.resultDegree
noncomputable def specialized (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) :=
  FormulaSignSlotRadialParameterEliminant.eliminant (pairFst c) a
    (FormulaSignSlotRadialEliminantInput.coordinate c)
noncomputable def Zero (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s t r : ℕ) : Prop :=
  (FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).eval₂ (Int.castRingHom ℝ) a = 0

theorem coefficient (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s t r : ℕ) :
    (((specialized c a).coeff s).coeff t).coeff r =
      (FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).eval₂ (Int.castRingHom ℝ) a :=
  FormulaSignSlotRadialCenterCoefficient.specialization c a s t r

theorem radius_degree (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s t : ℕ) :
    (((specialized c a).coeff s).coeff t).natDegree ≤ bound c := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  rw [coefficient, FormulaSignSlotRadialCenterCoefficient.zero_of_large_index c s t r (Or.inr (Or.inr hr))]
  exact MvPolynomial.eval₂_zero _ _

theorem target_degree (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s : ℕ) :
    ((specialized c a).coeff s).natDegree ≤ bound c := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro t ht
  ext r
  rw [Polynomial.coeff_zero, coefficient,
    FormulaSignSlotRadialCenterCoefficient.zero_of_large_index c s t r (Or.inr (Or.inl ht))]
  exact MvPolynomial.eval₂_zero _ _

theorem perturbation_degree (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) :
    (specialized c a).natDegree ≤ bound c := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro s hs
  ext t r
  rw [Polynomial.coeff_zero, Polynomial.coeff_zero, coefficient,
    FormulaSignSlotRadialCenterCoefficient.zero_of_large_index c s t r (Or.inl hs)]
  exact MvPolynomial.eval₂_zero _ _

theorem radius_zero_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s t : ℕ) :
    (∀ r < bound c + 1, Zero c a s t r) ↔ ((specialized c a).coeff s).coeff t = 0 := by
  constructor
  · intro H
    ext r
    rw [Polynomial.coeff_zero]
    by_cases hr : r < bound c + 1
    · exact (coefficient c a s t r).trans (H r hr)
    · exact coeff_eq_zero_of_natDegree_lt ((radius_degree c a s t).trans_lt (by omega))
  · intro H r _
    change _ = 0
    rw [← coefficient, H, Polynomial.coeff_zero]

theorem target_zero_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s : ℕ) :
    (∀ t < bound c + 1, ∀ r < bound c + 1, Zero c a s t r) ↔ (specialized c a).coeff s = 0 := by
  constructor
  · intro H
    apply Polynomial.ext
    intro t
    rw [Polynomial.coeff_zero]
    by_cases ht : t < bound c + 1
    · exact (radius_zero_iff c a s t).mp (H t ht)
    · exact coeff_eq_zero_of_natDegree_lt ((target_degree c a s).trans_lt (by omega))
  · intro H t _
    exact (radius_zero_iff c a s t).mpr (by rw [H, Polynomial.coeff_zero])

noncomputable def Guards (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau degree : ℕ) : Prop :=
  tau ≤ bound c ∧ degree ≤ bound c ∧
    (∀ k < tau, ∀ t < bound c + 1, ∀ r < bound c + 1, Zero c a k t r) ∧
    (∃ r < bound c + 1, ¬Zero c a tau degree r) ∧
    (∀ t < bound c + 1, degree < t → ∀ r < bound c + 1, Zero c a tau t r)

theorem guards_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau degree : ℕ) :
    Guards c a tau degree ↔ tau = (specialized c a).natTrailingDegree ∧
      degree = ((specialized c a).coeff tau).natDegree := by
  have HN : specialized c a ≠ 0 := FormulaSignSlotRadialParameterEliminant.eliminant_ne_zero _ _ _
  constructor
  · rintro ⟨_, _, HL, ⟨r, hr, HC⟩, HH⟩
    have HLeading : ((specialized c a).coeff tau).coeff degree ≠ 0 := by
      intro HZ
      apply HC
      change _ = 0
      rw [← coefficient, HZ, Polynomial.coeff_zero]
    have HChosen : (specialized c a).coeff tau ≠ 0 := by
      intro HZ
      exact HLeading (by rw [HZ, Polynomial.coeff_zero])
    have HT : tau = (specialized c a).natTrailingDegree := by
      apply Nat.le_antisymm
      · by_contra H
        have HZ := (target_zero_iff c a (specialized c a).natTrailingDegree).mp
          (HL (specialized c a).natTrailingDegree (by omega))
        exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr HN) HZ
      · exact Polynomial.natTrailingDegree_le_of_ne_zero HChosen
    refine ⟨HT, (natDegree_eq_of_le_of_coeff_ne_zero ?_ HLeading).symm⟩
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    by_cases htb : t < bound c + 1
    · exact (radius_zero_iff c a tau t).mp (HH t htb ht)
    · exact coeff_eq_zero_of_natDegree_lt ((target_degree c a tau).trans_lt (by omega))
  · rintro ⟨rfl, rfl⟩
    have HC : (specialized c a).coeff (specialized c a).natTrailingDegree ≠ 0 :=
      Polynomial.coeff_natTrailingDegree_ne_zero.mpr HN
    refine ⟨(natTrailingDegree_le_natDegree _).trans (perturbation_degree c a), target_degree c a _, ?_, ?_, ?_⟩
    · intro k hk
      exact (target_zero_iff c a k).mpr (coeff_eq_zero_of_lt_natTrailingDegree hk)
    · let L := ((specialized c a).coeff (specialized c a).natTrailingDegree).leadingCoeff
      have HNZ : L ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr HC
      have hr : L.coeff L.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr HNZ
      refine ⟨L.natDegree, Nat.lt_succ_of_le (radius_degree c a _ _), ?_⟩
      intro HZ
      apply hr
      exact (coefficient c a _ _ L.natDegree).trans HZ
    · intro t _ ht
      exact (radius_zero_iff c a _ t).mpr (coeff_eq_zero_of_natDegree_lt ht)

theorem exists_guards (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) :
    ∃ tau ≤ bound c, ∃ degree ≤ bound c, Guards c a tau degree := by
  have H := (guards_iff c a (specialized c a).natTrailingDegree
    ((specialized c a).coeff (specialized c a).natTrailingDegree).natDegree).mpr ⟨rfl, rfl⟩
  exact ⟨_, H.1, _, H.2.1, H⟩

theorem coordinate_at (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau degree : ℕ)
    (h : Guards c a tau degree) :
    FormulaSignSlotRadialParameterEliminant.coordinate (pairFst c) a
      (FormulaSignSlotRadialEliminantInput.coordinate c) =
        ((FormulaSignSlotRadialFormalEliminant.eliminant (pairFst c)
          (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff tau).map
            (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) := by
  have HT := (guards_iff c a tau degree).mp h |>.1
  change (specialized c a).coeff (specialized c a).natTrailingDegree = _
  rw [← HT]
  exact FormulaSignSlotRadialFormalEliminant.coefficient_specialization _ _ _ _

end LeanCanny.Encoding.FormulaSignSlotRadialCenterSelection
