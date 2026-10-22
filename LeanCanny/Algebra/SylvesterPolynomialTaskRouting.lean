/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SylvesterPolynomialSpace

/-! # The sole coefficient request of a polynomial Sylvester entry

Binary band guards select zero or one input-polynomial coefficient. These
writers expose that request without executing either coefficient reader.
-/

@[expose] public section

namespace LeanCanny.Algebra.SylvesterPolynomialBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation

attribute [local irreducible] BinaryNat.sub BinaryNat.add

/-- The first column block uses the right polynomial. -/
def selectRight (a : Access) : List Bool → Bool :=
  SylvesterBits.selectLeft a.scalarBits ∘ PolynomialMoment.augmentedInput

def rightInput (p : List Bool) : List Bool :=
  PolynomialMoment.vectorInput (SylvesterBits.coefficientInput SylvesterBits.col (PolynomialMoment.augmentedInput p))

def leftInput (a : Access) (p : List Bool) : List Bool :=
  PolynomialMoment.vectorInput (SylvesterBits.coefficientInput (SylvesterBits.rightShift a.scalarBits)
    (PolynomialMoment.augmentedInput p))

def active (a : Access) (p : List Bool) : Bool :=
  if selectRight a p then
    SylvesterBits.bandTest (SylvesterBits.rightDegree a.scalarBits) SylvesterBits.col (PolynomialMoment.augmentedInput p)
  else SylvesterBits.bandTest (SylvesterBits.leftDegree a.scalarBits) (SylvesterBits.rightShift a.scalarBits)
    (PolynomialMoment.augmentedInput p)

theorem selectRight_FP (a : Access) (ha : a.ControlsPolyTime) : (fun p => [selectRight a p]) ∈ FP :=
  mem_FP_comp PolynomialMoment.augmentedInput_mem_FP
    (SylvesterBits.selectLeft_mem_FP a.scalarBits (a.scalar_controls ha))

theorem rightInput_FP : rightInput ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp PolynomialMoment.augmentedInput_mem_FP
    (SylvesterBits.coefficientInput_mem_FP SylvesterBits.col_mem_FP)) PolynomialMoment.vectorInput_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem leftInput_FP (a : Access) (ha : a.ControlsPolyTime) : leftInput a ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp PolynomialMoment.augmentedInput_mem_FP
    (SylvesterBits.coefficientInput_mem_FP
      (SylvesterBits.rightShift_mem_FP_of_controls a.scalarBits (a.scalar_controls ha))))
    PolynomialMoment.vectorInput_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem active_FP (a : Access) (ha : a.ControlsPolyTime) : (fun p => [active a p]) ∈ FP := by
  have hr := mem_FP_comp PolynomialMoment.augmentedInput_mem_FP
    (SylvesterBits.bandTest_mem_FP (SylvesterBits.rightDegree_mem_FP_of_controls a.scalarBits (a.scalar_controls ha))
      SylvesterBits.col_mem_FP)
  have hl := mem_FP_comp PolynomialMoment.augmentedInput_mem_FP
    (SylvesterBits.bandTest_mem_FP (SylvesterBits.leftDegree_mem_FP_of_controls a.scalarBits (a.scalar_controls ha))
      (SylvesterBits.rightShift_mem_FP_of_controls a.scalarBits (a.scalar_controls ha)))
  have h := (flag_computable (selectRight_FP a ha)).ite' hr hl
  refine mem_FP_of_eq h ?_
  intro p
  cases hs : selectRight a p <;> simp only [active, hs, ite_true, Bool.false_eq_true, ite_false, Function.comp_apply]

theorem entry_eq (a : Access) (p : List Bool) : a.entry p =
    if active a p then
      if selectRight a p then a.rightCoefficient (rightInput p) else a.leftCoefficient (leftInput a p)
    else [] := by
  simp only [Access.entry, Access.scalarBits, selectRight, active, leftInput, rightInput,
    SylvesterBits.entry, SylvesterBits.selectLeft, SylvesterBits.bandEntry, SylvesterBits.bandTest,
    Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> simp_all
  all_goals
    rename_i htest
    have hband := of_decide_eq_true htest
    omega

theorem rightInput_context (p : List Bool) : pairFst (rightInput p) = pairFst p := by
  simp only [rightInput, PolynomialMoment.vectorInput, SylvesterBits.coefficientInput,
    PolynomialMoment.augmentedInput, pairFst_pair]

theorem leftInput_context (a : Access) (p : List Bool) : pairFst (leftInput a p) = pairFst p := by
  simp only [leftInput, PolynomialMoment.vectorInput, SylvesterBits.coefficientInput,
    PolynomialMoment.augmentedInput, pairFst_pair]

end LeanCanny.Algebra.SylvesterPolynomialBits.RecursiveStage
