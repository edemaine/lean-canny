/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterBounds
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterRows
/-! # Every retained parameter coefficient has an original-only degree bound -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterSupport
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantCoefficientModel
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem extract_integer (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    extract c r v (1 : FormulaSignSlotRadialFormalCenter.Radius c) =
      if r = 0 ∧ v = 0 then (1 : ℤ) else 0 := by
  change (((1 : Polynomial (MvPolynomial (Fin (d c)) ℤ)).coeff r).coeff v) = _
  by_cases hr : r = 0
  · subst r
    simp only [Polynomial.coeff_one_zero, MvPolynomial.coeff_one, true_and, eq_comm]
  · rw [Polynomial.coeff_one]
    simp only [hr, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, false_and]

private theorem extract_if (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ)
    (P : Prop) [Decidable P] (a b : FormulaSignSlotRadialFormalCenter.Radius c) :
    extract c r v (if P then a else b) =
      if P then extract c r v a else extract c r v b := by
  split_ifs <;> rfl

private theorem coordinate_coefficient (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (FormulaSignSlotRadialEliminantRows.polynomial c coordinate (CoerciveCriticalHomogenization.layout none)).coeff
      (FormulaSignSlotRadialEliminantRows.exponent (e.mapDomain CoerciveCriticalHomogenization.layout) s t r v) =
        (if s = 0 ∧ t = 1 ∧ e = Finsupp.single none 1 then (if r = 0 ∧ v = 0 then 1 else 0) else 0) -
        (if s = 0 ∧ t = 0 ∧ e = Finsupp.single (some coordinate) 1 then (if r = 0 ∧ v = 0 then 1 else 0) else 0) := by
  rw [FormulaSignSlotRadialEliminantRows.coefficient]
  change extract c r v ((((rename CoerciveCriticalHomogenization.layout
    (TiltedCoerciveCriticalFibers.nativeSystem
      ((FormulaSignSlotRadialFormalCenter.polynomial c).map ParametricTiltedCoerciveEliminant.constants)
      (degreeBudget c) (marginIndex c) Polynomial.X (Polynomial.C Polynomial.X) coordinate none)).coeff
      (e.mapDomain CoerciveCriticalHomogenization.layout)).coeff s).coeff t) = _
  rw [coeff_rename_mapDomain _ CoerciveCriticalHomogenization.layout.injective,
    ParametricTiltedCoerciveCoefficient.coordinate]
  simp only [map_sub, extract_if, map_zero, extract_integer]

theorem nested_bounds (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ)
    (H : (((((FormulaSignSlotRadialEliminantRows.system c coordinate row).coeff e).coeff s).coeff t).coeff r).coeff v ≠ 0) :
    s ≤ 2 ∧ t ≤ 1 ∧ r ≤ 2 * degreeBudget c ∧ ∀ i, v i ≤ 2 * degreeBudget c := by
  let f := e.mapDomain (CoerciveCriticalHomogenization.layout (n := FormulaSignSlotRadialFormalInput.spatial c)).symm
  have HF : f.mapDomain CoerciveCriticalHomogenization.layout = e := by
    ext i
    simp only [f, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have HN : (FormulaSignSlotRadialEliminantRows.polynomial c coordinate row).coeff
      (FormulaSignSlotRadialEliminantRows.exponent (f.mapDomain CoerciveCriticalHomogenization.layout) s t r v) ≠ 0 := by
    rw [FormulaSignSlotRadialEliminantRows.coefficient]
    have HH := congrArg (fun u : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ =>
      (((((FormulaSignSlotRadialEliminantRows.system c coordinate row).coeff u).coeff s).coeff t).coeff r).coeff v) HF
    intro HZ
    exact H (HH.symm.trans HZ)
  cases HT : CoerciveCriticalHomogenization.layout.symm row with
  | none =>
    have HR : row = CoerciveCriticalHomogenization.layout none := by
      rw [← HT, Equiv.apply_symm_apply]
    rw [HR, coordinate_coefficient] at HN
    have HS : s = 0 := by
      by_contra HS
      simp [HS] at HN
    have HU : t ≤ 1 := by
      by_contra HU
      have H0 : t ≠ 0 := by omega
      have H1 : t ≠ 1 := by omega
      simp [H0, H1] at HN
    have HV : r = 0 ∧ v = 0 := by
      by_contra HV
      simp [HV] at HN
    rcases HV with ⟨rfl, rfl⟩
    exact ⟨by omega, HU, Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | some j =>
    have HR : row = CoerciveCriticalHomogenization.layout (some j) := by
      rw [← HT, Equiv.apply_symm_apply]
    rw [HR, gradient_eq] at HN
    obtain ⟨HS, HU, HV⟩ := FormulaSignSlotRadialEliminantParameterBounds.gradient_bounds c j f s t r v HN
    exact ⟨HS, by omega, HV⟩

theorem coordinate_bound (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ)
    (f : Fin (d c + 3) →₀ ℕ)
    (H : f ∈ ((FormulaSignSlotRadialEliminantParameterRows.row c coordinate row).coeff e).support)
    (i : Fin (d c + 3)) : f i ≤ 2 * degreeBudget c + 2 := by
  have HF : TriplePolynomialParameterFlatten.exponent (f 0) (f.tail 0) (f.tail.tail 0)
      f.tail.tail.tail = f := by
    simp only [TriplePolynomialParameterFlatten.exponent, Finsupp.cons_tail]
  have HN : (((((FormulaSignSlotRadialEliminantRows.system c coordinate row).coeff e).coeff (f 0)).coeff
      (f.tail 0)).coeff (f.tail.tail 0)).coeff f.tail.tail.tail ≠ 0 := by
    rw [← FormulaSignSlotRadialEliminantParameterRows.coefficient, HF]
    exact mem_support_iff.mp H
  obtain ⟨HS, HT, HR, HV⟩ := nested_bounds c coordinate row e _ _ _ _ HN
  refine Fin.cases (by omega) (fun i => ?_) i
  refine Fin.cases (by simpa only [← Finsupp.tail_apply] using HT.trans (by omega)) (fun i => ?_) i
  refine Fin.cases (by simpa only [← Finsupp.tail_apply] using HR.trans (Nat.le_add_right _ _)) (fun i => ?_) i
  simpa only [← Finsupp.tail_apply] using (HV i).trans (Nat.le_add_right _ _)

noncomputable def degree (c : List Bool) : ℕ := (d c + 3) * (2 * degreeBudget c + 2)

theorem degree_bound (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ) :
    ((FormulaSignSlotRadialEliminantParameterRows.row c coordinate row).coeff e).totalDegree ≤ degree c := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro f hf
  rw [Finsupp.sum_fintype _ _ (by simp)]
  have H := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => coordinate_bound c coordinate row e f hf i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, degree] using H

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterSupport
