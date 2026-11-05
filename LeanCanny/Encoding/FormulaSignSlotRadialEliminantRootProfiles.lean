/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSliceSource
/-! # Actual eliminant budgets ignore the observable coordinate selector -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
open LeanCanny.Algebra LeanCanny.Connectivity
set_option backward.isDefEq.respectTransparency false

theorem columns_eq (c e : List Bool) (H : pairFst c=pairFst e) :
    FormulaSignSlotRadialEliminantPackingLayout.columns c=FormulaSignSlotRadialEliminantPackingLayout.columns e := by
  simp only [FormulaSignSlotRadialEliminantPackingLayout.columns,FormulaSignSlotRadialEliminantPackingLayout.width,
    FormulaSignSlotRadialEliminantPackingLayout.spatial,FormulaSignSlotRadialEliminantPackingLayout.sourceDegree,H]

theorem width_eq (c e : List Bool) (H : pairFst c=pairFst e) :
    FormulaSignSlotRadialEliminantPackingLayout.parameterWidth c=
      FormulaSignSlotRadialEliminantPackingLayout.parameterWidth e := by
  simp only [FormulaSignSlotRadialEliminantPackingLayout.parameterWidth,
    FormulaSignSlotRadialEliminantPackingLayout.columnExponent,FormulaSignSlotRadialEliminantPackingLayout.width,
    FormulaSignSlotRadialEliminantPackingLayout.spatial,FormulaSignSlotRadialEliminantPackingLayout.sourceDegree,
    FormulaSignSlotRadialEliminantPackingLayout.parameterDegree,H]

theorem degree_eq (c e : List Bool) (H : pairFst c=pairFst e) :
    FormulaSignSlotRadialEliminantPacked.resultDegree c=FormulaSignSlotRadialEliminantPacked.resultDegree e := by
  simp only [FormulaSignSlotRadialEliminantPacked.resultDegree,columns_eq c e H,
    FormulaSignSlotRadialEliminantPackingLayout.parameterDegree,H]

theorem mass_eq (c e : List Bool) (H : pairFst c=pairFst e) :
    FormulaSignSlotRadialEliminantFormalMass.budget c=FormulaSignSlotRadialEliminantFormalMass.budget e := by
  simp only [FormulaSignSlotRadialEliminantFormalMass.budget,FormulaSignSlotRadialEliminantMass.resultBudget,
    FormulaSignSlotRadialEliminantMass.rowBudget,width_eq c e H,columns_eq c e H,H]

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
