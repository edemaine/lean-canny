/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSquarefreeSelection
public import LeanCanny.Algebra.DomainSquarefreeLeadingCoefficient
public import LeanCanny.Geometry.RealParameterRootBranches
/-! # Exact formal-center coefficients of the actual branch cut

The GCD index and degree are validated at the same real center. The resulting
integer polynomial maps to the literal branch cut, including constant inputs.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCut
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity Polynomial PrincipalSubresultant
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

theorem cut_formula (p : Polynomial (Polynomial ℝ)) :
    RealParameterRootBranches.cut p = if p.natDegree = 0 then p.leadingCoeff else
      p.leadingCoeff ^ 2 * psc p p.derivative p.natDegree (p.natDegree - 1)
        (DomainSquarefree.index p) ^ (p.natDegree - DomainSquarefree.index p + 1) := by
  by_cases h : p.natDegree = 0
  · simp only [RealParameterRootBranches.cut, RealParameterRootBranches.auxiliary,
      DomainSquarefree.exceptional, DomainSquarefree.polynomial, ite_eq_left h,
      Polynomial.leadingCoeff_one, mul_one]
  · rw [ite_eq_right h, RealParameterRootBranches.cut, RealParameterRootBranches.auxiliary,
      DomainSquarefree.exceptional, ite_eq_right h, DomainSquarefree.leading_coefficient p h,
      pow_succ]
    ring

noncomputable def polynomial (c : List Bool) (tau D k : ℕ) :=
  if D = 0 then (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial c tau D).coeff 0
  else if k < D then
    (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial c tau D).coeff D ^ 2 *
      FormulaSignSlotRadialCenterSquarefreeSelection.principal c tau D k ^ (D - k + 1)
  else 0

theorem specialization (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D k : ℕ)
    (h : FormulaSignSlotRadialCenterSquarefreeSelection.Guards c a tau D k) :
    (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a) (polynomial c tau D k) =
      RealParameterRootBranches.cut (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a) := by
  have HD := FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree c a tau D h.1
  have HK := (FormulaSignSlotRadialCenterSquarefreeSelection.guards_iff c a tau D k).mp h |>.2
  have HC : (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst c) a)
      ((FormulaSignSlotRadialCenterSquarefreeSelection.polynomial c tau D).coeff D) =
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff := by
    rw [← Polynomial.coeff_map,
      FormulaSignSlotRadialCenterSquarefreeSelection.polynomial_map c a tau D h.1,
      Polynomial.leadingCoeff, HD]
  rw [cut_formula, HD, polynomial]
  by_cases HZ : D = 0
  · rw [ite_eq_left HZ, ite_eq_left HZ]
    simpa only [HZ] using HC
  · have HL : k < D := by
      have HH := h.2
      rw [ite_eq_right HZ] at HH
      exact HH.1
    rw [ite_eq_right HZ, ite_eq_right HZ, ite_eq_left HL, map_mul, map_pow, HC,
      map_pow, FormulaSignSlotRadialCenterSquarefreeSelection.principal_map c a tau D k h.1,
      HK]

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCut
