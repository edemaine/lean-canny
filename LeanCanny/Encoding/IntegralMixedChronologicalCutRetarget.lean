/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
public import LeanCanny.Encoding.IntegralMixedChronologicalChosenCutCode
/-! # The raw ordinary probe changes only the unused sweep companion field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory IntegralMixedRelativeCuts
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem raw_base_good (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : Good n birth w g j) : Good n birth w g g:=
 ⟨H.1,H.2.1,H.2.2.1,H.2.1,H.2.2.1⟩

theorem raw_rule_retarget {n birth S B : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B birth ι) (w : List Bool) (g j : ℕ) (H : Good n birth w g j) :
    (rawData n birth w g j H).rule (commonDenominator x) (commonDenominator_ne_zero x)=
      IntegralMixedSweepRetarget.rule
        ((rawData n birth w g g (raw_base_good n birth w g j H)).rule
          (commonDenominator x) (commonDenominator_ne_zero x))
        (j-(WordListRecords.count w+1)):=by
 unfold rawData
 rw [data_rule,data_rule]
 simp only [IntegralMixedChronologicalFrameCode.descriptor_length]
 rfl

theorem raw_chosenCode_actual {n birth : ℕ} (w : List Bool) (g : ℕ) (H : Good n birth w g g)
    (P : SpatialSource n) (Q : ℤ) (hQ : Q≠0)
    (c : Kind P ((rawData n birth w g g H).rule Q hQ)) (degree : ℕ) :
    (rawData n birth w g g H).chosenCode Q hQ c degree=
      code n w g
        (WordListRecords.count w+1+IntegralMixedSweepRetarget.coordinateIndex
          ((rawData n birth w g g H).rule Q hQ) c)
        (IntegralMixedCutRecordConstructor.tagIndex
          (IntegralMixedSweepRetarget.tag ((rawData n birth w g g H).rule Q hQ) c))
        (IntegralMixedSweepRetarget.choiceIndex ((rawData n birth w g g H).rule Q hQ) c) degree:=by
 unfold rawData
 rw [chosenCode_actual,code_descriptor]
 simp only [physicalCoordinate,pointData_offset,IntegralMixedChronologicalFrameCode.descriptor_length]
 cases c <;>rfl

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode
