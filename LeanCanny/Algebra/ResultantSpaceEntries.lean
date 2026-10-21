/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerDeterminantSpaceEntries
public import LeanCanny.Algebra.SylvesterSpaceAccess

/-!
# Resultant zero testing with space-bounded coefficient routines

FP degree and coefficient-budget fields suffice when both coefficient residue
functions have certified space evaluators. The Sylvester accessor, determinant
factor/moment pipeline, and modulus scan retain all resource certificates.
-/

@[expose] public section

namespace LeanCanny.Algebra.Resultant.Access
open Complexity
open LeanCanny.Computation

theorem integer_controls {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime) :
    a.integer.ControlsPolyTime := by
  constructor
  · simpa only [integer] using SylvesterBits.dimension_mem_FP_of_controls a.bits ha
  · simpa only [integer] using SylvesterBits.budget_mem_FP_of_controls a.bits ha

theorem deciderWithCoefficients {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    SpaceDecider F.zeroLanguage :=
  Berkowitz.IntegerAccess.deciderWithEntry a.integer (integer_controls a ha) (integer_entryEvaluator a ha L R)

theorem zeroLanguage_mem_PSPACE_of_evaluators {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    F.zeroLanguage ∈ PSPACE := (deciderWithCoefficients a ha L R).mem_PSPACE

theorem standardZeroLanguage_mem_PSPACE_of_evaluators {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient)
    (hm : ∀ c, F.leftDegree c = (F.left c).natDegree)
    (hn : ∀ c, F.rightDegree c = (F.right c).natDegree) : F.standardZeroLanguage ∈ PSPACE := by
  have h : F.zeroLanguage = F.standardZeroLanguage := by
    ext c
    simp only [Family.zeroLanguage, Family.standardZeroLanguage, hm, hn]
  rw [← h]
  exact zeroLanguage_mem_PSPACE_of_evaluators a ha L R

end LeanCanny.Algebra.Resultant.Access
