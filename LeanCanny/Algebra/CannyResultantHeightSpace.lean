/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyResultantInteger
public import LeanCanny.Algebra.CannyCoefficientSpace

/-! # Resultant height writers independent of coefficient running time -/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.IntegerAccess
open LeanCanny.Encoding
attribute [local irreducible] BinaryNat.add BinaryNat.mul

structure ControlsPolyTime {F : BoundedFamily} (a : IntegerAccess F) : Prop where
  residue : a.residue.ControlsPolyTime
  leftBits : a.leftBits ∈ FP
  rightBits : a.rightBits ∈ FP

theorem dimension_mem_FP_of_controls {F : BoundedFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime) : a.dimension ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.residue.leftDegree ha.residue.rightDegree) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.dimension) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem shiftBudget_mem_FP_of_controls {F : BoundedFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime) : a.shiftBudget ∈ FP := by
  have hsd := sizeField_mem_FP (mem_FP_comp ha.residue.leftDegree BinaryNat.succ_mem_FP)
  have hsc := sizeField_mem_FP (mem_FP_comp ha.residue.direction BinaryNat.succ_mem_FP)
  have hb := mem_FP_comp ha.leftBits BinaryNat.succ_mem_FP
  have hp := mem_FP_comp (mem_FP_pair hsc ha.residue.leftDegree) BinaryNat.mul_mem_FP
  have hl := mem_FP_comp (mem_FP_pair hsd ha.residue.leftDegree) BinaryNat.add_mem_FP
  have hr := mem_FP_comp (mem_FP_pair hb hp) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hl hr) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.shiftBudget) h ?_
  intro c
  simp only [Function.comp_apply, shiftBudget]

theorem budget_mem_FP_of_controls {F : BoundedFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime) : a.budget ∈ FP := by
  have hn := dimension_mem_FP_of_controls a ha
  have hs := sizeField_mem_FP hn
  have hf := mem_FP_comp (mem_FP_pair hs hn) BinaryNat.mul_mem_FP
  have hl := mem_FP_comp (mem_FP_pair ha.residue.rightDegree (shiftBudget_mem_FP_of_controls a ha)) BinaryNat.mul_mem_FP
  have hb := mem_FP_comp ha.rightBits BinaryNat.succ_mem_FP
  have hr := mem_FP_comp (mem_FP_pair ha.residue.leftDegree hb) BinaryNat.mul_mem_FP
  have hfl := mem_FP_comp (mem_FP_pair hf hl) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hfl hr) BinaryNat.add_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := a.budget) h ?_
  intro c
  simp only [Function.comp_apply, budget]

end LeanCanny.Algebra.CannyResultantBits.IntegerAccess
