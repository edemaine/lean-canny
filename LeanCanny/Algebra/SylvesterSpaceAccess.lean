/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantPSPACE
public import LeanCanny.Computation.SpaceFunctionBranch

/-!
# Sylvester entries through space-bounded coefficient routines

The degree and coefficient-budget fields remain FP. Each selected coefficient
may instead be returned by a certified space routine. Explicit branch tags and
the prepared-query length bounds account for every child state and its clock.
The resulting entry function is the same function whose matrix semantics were
proved in `SylvesterAccessCorrect`.
-/

@[expose] public section

namespace LeanCanny.Algebra.SylvesterBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

structure Access.ControlsPolyTime (a : Access) : Prop where
  leftDegree : a.leftDegree ∈ FP
  rightDegree : a.rightDegree ∈ FP
  coefficientBits : a.coefficientBits ∈ FP

def withoutCoefficients (a : Access) : Access :=
  { a with leftCoefficient := fun _ => [], rightCoefficient := fun _ => [] }

theorem withoutCoefficients_polyTime (a : Access) (ha : a.ControlsPolyTime) :
    (withoutCoefficients a).PolyTime :=
  ⟨ha.leftDegree, ha.rightDegree, ha.coefficientBits, constFn_mem_FP [], constFn_mem_FP []⟩

theorem leftDegree_mem_FP_of_controls (a : Access) (ha : a.ControlsPolyTime) : leftDegree a ∈ FP := by
  have h := leftDegree_mem_FP (withoutCoefficients a) (withoutCoefficients_polyTime a ha)
  refine mem_FP_of_eq (g := leftDegree a) h ?_
  intro p
  simp only [withoutCoefficients, leftDegree]

theorem rightDegree_mem_FP_of_controls (a : Access) (ha : a.ControlsPolyTime) : rightDegree a ∈ FP := by
  have h := rightDegree_mem_FP (withoutCoefficients a) (withoutCoefficients_polyTime a ha)
  refine mem_FP_of_eq (g := rightDegree a) h ?_
  intro p
  simp only [withoutCoefficients, rightDegree]

theorem rightShift_mem_FP_of_controls (a : Access) (ha : a.ControlsPolyTime) : rightShift a ∈ FP := by
  have h := rightShift_mem_FP (withoutCoefficients a) (withoutCoefficients_polyTime a ha)
  refine mem_FP_of_eq (g := rightShift a) h ?_
  intro p
  simp only [withoutCoefficients, rightShift, leftDegree]

theorem dimension_mem_FP_of_controls (a : Access) (ha : a.ControlsPolyTime) : dimension a ∈ FP := by
  have h := dimension_mem_FP (withoutCoefficients a) (withoutCoefficients_polyTime a ha)
  refine mem_FP_of_eq (g := dimension a) h ?_
  intro p
  simp only [withoutCoefficients, dimension]

theorem budget_mem_FP_of_controls (a : Access) (ha : a.ControlsPolyTime) : budget a ∈ FP := by
  have h := budget_mem_FP (withoutCoefficients a) (withoutCoefficients_polyTime a ha)
  refine mem_FP_of_eq (g := budget a) h ?_
  intro p
  simp only [withoutCoefficients, budget, dimensionSize, dimension]

def bandTest (width shift : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (shift p) ≤ Nat.fromBitsLE (row p) ∧
    Nat.fromBitsLE (row p) ≤ Nat.fromBitsLE (bandEnd width shift p))

theorem bandTest_mem_FP {width shift : List Bool → List Bool} (hw : width ∈ FP) (hs : shift ∈ FP) :
    (fun p => [bandTest width shift p]) ∈ FP :=
  ((BinaryNat.le_fppred hs row_mem_FP).and
    (BinaryNat.le_fppred row_mem_FP (bandEnd_mem_FP hw hs))).flag_mem_FP

noncomputable def bandEvaluator {coefficient width shift : List Bool → List Bool}
    (E : SpaceFunction coefficient) (hw : width ∈ FP) (hs : shift ∈ FP) :
    SpaceFunction (bandEntry coefficient width shift) := by
  have R := SpaceFunction.branch (bandTest width shift) (bandTest_mem_FP hw hs)
    (E.precompose (coefficientInput shift) (coefficientInput_mem_FP hs))
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine R.congr ?_
  funext p
  simp only [bandTest, bandEntry, Function.comp_apply, decide_eq_true_eq]

def selectLeft (a : Access) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (col p) < Nat.fromBitsLE (leftDegree a p))

theorem selectLeft_mem_FP (a : Access) (ha : a.ControlsPolyTime) :
    (fun p => [selectLeft a p]) ∈ FP :=
  (BinaryNat.lt_fppred col_mem_FP (leftDegree_mem_FP_of_controls a ha)).flag_mem_FP

noncomputable def entryEvaluator (a : Access) (ha : a.ControlsPolyTime)
    (L : SpaceFunction a.leftCoefficient) (R : SpaceFunction a.rightCoefficient) : SpaceFunction (entry a) := by
  have ER := bandEvaluator R (rightDegree_mem_FP_of_controls a ha) col_mem_FP
  have EL := bandEvaluator L (leftDegree_mem_FP_of_controls a ha) (rightShift_mem_FP_of_controls a ha)
  have E := SpaceFunction.branch (selectLeft a) (selectLeft_mem_FP a ha) ER EL
  refine E.congr ?_
  funext p
  simp only [selectLeft, entry, decide_eq_true_eq]

end LeanCanny.Algebra.SylvesterBits

namespace LeanCanny.Algebra.Resultant.Access
open LeanCanny.Computation

noncomputable def integer_entryEvaluator {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    SpaceFunction a.integer.entry := by
  have E := SylvesterBits.entryEvaluator a.bits ha L R
  refine E.congr ?_
  funext p
  simp only [integer]

end LeanCanny.Algebra.Resultant.Access
