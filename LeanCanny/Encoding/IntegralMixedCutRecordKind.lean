/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCutRecordConstructor
public import LeanCanny.Algebra.IntegralMixedSweepRetargetRealization
/-! # All four chosen cut kinds decode to the exact retargeted command

Field4 is intentionally shared with the sweep's unused critical companion
coordinate. The chosen Kind supplies that field; no other rule field or
source is changed, and the selected stored degree is copied literally.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCutRecordConstructor
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCausalRecordBits IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Data.retarget {n birth : ℕ} (d : Data n birth)
    (j : Fin (n-d.critical.offset.val+1)) : Data n birth where
  critical:={d.critical with coordinate:=j}
  positive:=d.positive
  height:=d.height
  current:=d.current

theorem Data.rule_retarget {n birth : ℕ} (d : Data n birth) (Q : ℤ) (hQ : Q≠0)
    (j : Fin (n-d.critical.offset.val+1)) :
    (d.retarget j).rule Q hQ=IntegralMixedSweepRetarget.rule (d.rule Q hQ) j.val:=rfl

def Data.coordinate {n birth : ℕ} {P : SpatialSource n} (d : Data n birth) (Q : ℤ) (hQ : Q≠0) :
    Kind P (d.rule Q hQ)→Fin (n-d.critical.offset.val+1)
  | .coordinate j _=>j
  | .squarefree j _=>j
  | .value j _=>j
  | .limitCoordinate j _=>j

noncomputable def Data.chosenCode {n birth : ℕ} {P : SpatialSource n} (d : Data n birth)
    (Q : ℤ) (hQ : Q≠0) (c : Kind P (d.rule Q hQ)) (degree : ℕ) : List Bool:=
  (d.retarget (d.coordinate Q hQ c)).code (IntegralMixedSweepRetarget.tag (d.rule Q hQ) c)
    (IntegralMixedSweepRetarget.choiceIndex (d.rule Q hQ) c) degree

theorem chosen_command {n birth B : ℕ} (d : Data n birth) (P : SpatialSource n) (Q : ℤ) (hQ : Q≠0)
    (c : Kind P (d.rule Q hQ)) (degree : ℕ)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (IntegralMixedCausalUnitRecordBits.record P d.ambient_positive birth (d.chosenCode Q hQ c degree) hcap).template.command Q hQ=
      .cut (IntegralMixedSweepRetarget.rule (d.rule Q hQ) (IntegralMixedSweepRetarget.coordinateIndex (d.rule Q hQ) c))
        (IntegralMixedSweepRetarget.kind (d.rule Q hQ) (IntegralMixedSweepRetarget.coordinateIndex (d.rule Q hQ) c) c)
        degree hd (hd.trans hcap):=by
  unfold Data.chosenCode
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,field_0,
    show ([] : List Bool)[0]?.getD false=false from rfl,Bool.false_eq_true,ite_false,Template.command]
  rw [cut_decode _ P _ _ degree hd hcap]
  dsimp only [Data.rule,IntegralMixedCriticalRecordConstructor.Data.rule] at c
  cases c <;> simp only [Data.cut,Cut.rule,Cut.kind,Data.retarget,Data.rule,
    IntegralMixedCriticalRecordConstructor.Data.rule,IntegralMixedSweepRetarget.tag,
    IntegralMixedSweepRetarget.choiceIndex,IntegralMixedSweepRetarget.coordinateIndex,
    IntegralMixedSweepRetarget.kind,IntegralMixedSweepRetarget.rule,Data.coordinate]
  all_goals rename_i j i
  all_goals simp only [Nat.mod_eq_of_lt j.isLt,Nat.mod_eq_of_lt i.isLt]
  simp only [IntegralMixedValueTrailing.ChoiceBound,IntegralMixedGridValue.dimension,
    IntegralMixedGridValue.width,IntegralMixedCoordinateSquarefree.coordinateDegree] at i ⊢
  simp only [Nat.mod_eq_of_lt i.isLt]

end LeanCanny.Encoding.IntegralMixedCutRecordConstructor
