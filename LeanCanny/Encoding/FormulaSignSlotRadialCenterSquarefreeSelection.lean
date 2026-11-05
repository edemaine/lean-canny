/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSelection
public import LeanCanny.Algebra.DomainSquarefree
/-! # Same-center principal guards for the actual radial squarefree cut

The target polynomial is truncated to the degree validated after center
specialization. Principal tests are also specialized at that same center.
Thus no symbolic degree or symbolic GCD index is copied through a real map.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterSquarefreeSelection
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial PrincipalSubresultant
open FormulaSignSlotCenteredRadialGraph
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

noncomputable def truncate {R : Type*} [Semiring R] (p : Polynomial R) (D : ℕ) : Polynomial R :=
  ∑ j ∈ Finset.range (D + 1), Polynomial.monomial j (p.coeff j)

theorem truncate_coefficient {R : Type*} [Semiring R] (p : Polynomial R) (D j : ℕ) :
    (truncate p D).coeff j = if j ≤ D then p.coeff j else 0 := by
  simp [truncate, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem truncate_degree {R : Type*} [Semiring R] (p : Polynomial R) (D : ℕ) :
    (truncate p D).natDegree ≤ D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [truncate_coefficient, ite_eq_right (by omega)]

noncomputable def polynomial (c : List Bool) (tau D : ℕ) :=
  truncate ((FormulaSignSlotRadialFormalEliminant.eliminant (pairFst c)
    (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff tau) D

noncomputable def coordinate (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) :=
  FormulaSignSlotRadialParameterEliminant.coordinate (pairFst c) a
    (FormulaSignSlotRadialEliminantInput.coordinate c)

theorem polynomial_map (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D : ℕ)
    (h : FormulaSignSlotRadialCenterSelection.Guards c a tau D) :
    (polynomial c tau D).map (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) = coordinate c a := by
  have HE := FormulaSignSlotRadialCenterSelection.coordinate_at c a tau D h
  have HD := (FormulaSignSlotRadialCenterSelection.guards_iff c a tau D).mp h |>.2
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map, polynomial, truncate_coefficient]
  by_cases hj : j ≤ D
  · rw [ite_eq_left hj]
    simpa only [coordinate, Polynomial.coeff_map] using (congrArg (fun q => q.coeff j) HE).symm
  · rw [ite_eq_right hj, map_zero]
    have HC : coordinate c a = (FormulaSignSlotRadialCenterSelection.specialized c a).coeff tau := by
      exact HE.trans (FormulaSignSlotRadialFormalEliminant.coefficient_specialization _ _ _ _).symm
    rw [HC]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

noncomputable def principal (c : List Bool) (tau D j : ℕ) :=
  psc (polynomial c tau D) (polynomial c tau D).derivative D (D - 1) j

theorem principal_map (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D j : ℕ)
    (h : FormulaSignSlotRadialCenterSelection.Guards c a tau D) :
    (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) (principal c tau D j) =
      psc (coordinate c a) (coordinate c a).derivative D (D - 1) j := by
  rw [principal, ← psc_map_map, ← Polynomial.derivative_map, polynomial_map c a tau D h]

noncomputable def Guards (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D k : ℕ) : Prop :=
  FormulaSignSlotRadialCenterSelection.Guards c a tau D ∧
    if D = 0 then k = 0 else k < D ∧
      (∀ j < k, (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) (principal c tau D j) = 0) ∧
      (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) (principal c tau D k) ≠ 0

private theorem index_iff {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (D k : ℕ) (hD : p.natDegree = D) (hp : D ≠ 0) :
    (k < D ∧ (∀ j < k, psc p p.derivative D (D - 1) j = 0) ∧
      psc p p.derivative D (D - 1) k ≠ 0) ↔ k = DomainSquarefree.index p := by
  have HV := DomainSquarefree.valid_fraction p (by omega)
  rw [hD] at HV
  have HZ (j : ℕ) : DomainSquarefree.embedding (psc p p.derivative D (D - 1) j) = 0 ↔
      psc p p.derivative D (D - 1) j = 0 :=
    map_eq_zero_iff _ DomainSquarefree.embedding_injective
  constructor
  · rintro ⟨_, HL, HS⟩
    apply Nat.le_antisymm
    · by_contra HH
      exact (HZ _).not.mp HV.selected (HL _ (by omega))
    · by_contra HH
      exact HS ((HZ _).mp (HV.lower _ (by omega)))
  · rintro rfl
    exact ⟨HV.index_lt, fun j hj => (HZ j).mp (HV.lower j hj), (HZ _).not.mp HV.selected⟩

theorem guards_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D k : ℕ) :
    Guards c a tau D k ↔ FormulaSignSlotRadialCenterSelection.Guards c a tau D ∧
      k = DomainSquarefree.index (coordinate c a) := by
  constructor
  · rintro ⟨HS, HK⟩
    have HD : (coordinate c a).natDegree = D := by
      have HE := FormulaSignSlotRadialCenterSelection.coordinate_at c a tau D HS
      have HC : coordinate c a = (FormulaSignSlotRadialCenterSelection.specialized c a).coeff tau :=
        HE.trans (FormulaSignSlotRadialFormalEliminant.coefficient_specialization _ _ _ _).symm
      rw [HC]
      exact ((FormulaSignSlotRadialCenterSelection.guards_iff c a tau D).mp HS |>.2).symm
    refine ⟨HS, ?_⟩
    by_cases hD : D = 0
    · simpa only [hD, ite_true, DomainSquarefree.index, HD, dite_true] using HK
    · rw [ite_eq_right hD] at HK
      apply (index_iff (coordinate c a) D k HD hD).mp
      simpa only [principal_map c a tau D _ HS] using HK
  · rintro ⟨HS, HK⟩
    refine ⟨HS, ?_⟩
    have HD : (coordinate c a).natDegree = D := by
      have HE := FormulaSignSlotRadialCenterSelection.coordinate_at c a tau D HS
      have HC : coordinate c a = (FormulaSignSlotRadialCenterSelection.specialized c a).coeff tau :=
        HE.trans (FormulaSignSlotRadialFormalEliminant.coefficient_specialization _ _ _ _).symm
      rw [HC]
      exact ((FormulaSignSlotRadialCenterSelection.guards_iff c a tau D).mp HS |>.2).symm
    by_cases hD : D = 0
    · simpa only [hD, ite_true, DomainSquarefree.index, HD, dite_true] using HK
    · rw [ite_eq_right hD]
      have H := (index_iff (coordinate c a) D k HD hD).mpr HK
      simpa only [principal_map c a tau D _ HS] using H

theorem coordinate_degree (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D : ℕ)
    (h : FormulaSignSlotRadialCenterSelection.Guards c a tau D) : (coordinate c a).natDegree = D := by
  have HE := FormulaSignSlotRadialCenterSelection.coordinate_at c a tau D h
  have HC : coordinate c a = (FormulaSignSlotRadialCenterSelection.specialized c a).coeff tau :=
    HE.trans (FormulaSignSlotRadialFormalEliminant.coefficient_specialization _ _ _ _).symm
  rw [HC]
  exact ((FormulaSignSlotRadialCenterSelection.guards_iff c a tau D).mp h |>.2).symm

noncomputable def squarefree (c : List Bool) (tau D k : ℕ) :=
  if D = 0 then 1 else ValidatedSquarefreeSpecialization.polynomial (polynomial c tau D) D k

noncomputable def exceptional (c : List Bool) (tau D k : ℕ) :=
  (polynomial c tau D).coeff D * if D = 0 then 1 else principal c tau D k

theorem squarefree_map (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D k : ℕ)
    (h : Guards c a tau D k) :
    (squarefree c tau D k).map (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) =
      DomainSquarefree.polynomial (coordinate c a) := by
  have HK := (guards_iff c a tau D k).mp h |>.2
  have HD := coordinate_degree c a tau D h.1
  rw [squarefree, DomainSquarefree.polynomial, HD]
  split_ifs
  · exact Polynomial.map_one _
  · rw [ValidatedSquarefreeSpecialization.polynomial, ScaledPolynomialQuotient.quotient_map,
      ValidatedSquarefreeSpecialization.gcd, coefficientForm_map, ← Polynomial.derivative_map,
      polynomial_map c a tau D h.1, HK]
    rfl

theorem exceptional_map (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D k : ℕ)
    (h : Guards c a tau D k) :
    (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) (exceptional c tau D k) =
      DomainSquarefree.exceptional (coordinate c a) := by
  have HK := (guards_iff c a tau D k).mp h |>.2
  have HD := coordinate_degree c a tau D h.1
  have HC : (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) ((polynomial c tau D).coeff D) =
      (coordinate c a).coeff D := by
    rw [← Polynomial.coeff_map, polynomial_map c a tau D h.1]
  rw [exceptional, map_mul, HC, DomainSquarefree.exceptional, Polynomial.leadingCoeff, HD]
  split_ifs
  · rw [map_one]
  · rw [principal_map c a tau D k h.1, HK]

theorem exists_guards (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) :
    ∃ tau ≤ FormulaSignSlotRadialCenterSelection.bound c,
      ∃ D ≤ FormulaSignSlotRadialCenterSelection.bound c,
        ∃ k ≤ D, Guards c a tau D k := by
  obtain ⟨tau, ht, D, hD, HS⟩ := FormulaSignSlotRadialCenterSelection.exists_guards c a
  have HD := coordinate_degree c a tau D HS
  refine ⟨tau, ht, D, hD, DomainSquarefree.index (coordinate c a), ?_, (guards_iff _ _ _ _ _).mpr ⟨HS, rfl⟩⟩
  by_cases hD0 : D = 0
  · simp only [DomainSquarefree.index, HD, hD0, dite_true]
    rfl
  · exact (DomainSquarefree.valid_fraction (coordinate c a) (by omega)).index_lt.le.trans HD.le

end LeanCanny.Encoding.FormulaSignSlotRadialCenterSquarefreeSelection
