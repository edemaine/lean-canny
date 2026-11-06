/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointComponentTransport
/-! # A literal joint equation root gives the exact finite core point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCorePoint
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def ofEnvironment (u : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation u).eval env = 0) :
    AuxiliaryCandidateComponentCover.Space FormulaSignSlotRadialJointLayout.dimension
      FormulaSignSlotRadialJointCore.equation u := by
  refine ⟨fun i => env i.val, ?_⟩
  change (AuxiliaryTiltedTerm.polynomial (FormulaSignSlotRadialJointLayout.dimension u)
    (FormulaSignSlotRadialJointCore.equation u)).eval (fun i => env i.val) = 0
  rw [AuxiliaryCandidateComponentCover.evaluation]
  have HE := (FormulaSignSlotRadialJointCore.equation u).eval_congr
    (Formula.extend (fun i : Fin (FormulaSignSlotRadialJointLayout.dimension u) => env i.val)) env (by
      intro i hi
      simp only [Formula.extend, dite_eq_left (hi.trans_le (FormulaSignSlotRadialJointCore.scope u))])
  exact HE.trans h

theorem project_ofEnvironment (side : Bool) (u : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation u).eval env = 0) :
    FormulaSignSlotRadialJointComponentTransport.project side u (ofEnvironment u env h) =
      FormulaSignSlotRadialJointGeometry.closedPoint side u env h := by
  apply Subtype.ext
  funext i
  exact FormulaSignSlotRadialJointComponentTransport.project_coordinate side u (ofEnvironment u env h) i

end LeanCanny.Encoding.FormulaSignSlotRadialJointCorePoint
