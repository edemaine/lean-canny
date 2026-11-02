/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedEmptyUnitData
public import LeanCanny.Algebra.IntegralMixedFramedUnitControls
/-! # Empty-prelude canonical records produce their unit snapshot -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open scoped Classical

variable (P : Parameters) (O : Originals P)
  (hn : ∀ root, 0<P.ambient root)
  (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (hroom : ∀ root, count root+2≤P.cap root+1)
  (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root)

private theorem expression_congr (w v : List Bool → List Bool) (key : List Bool) (hw : w key=v key)
    (physical : Bool) (i : ℕ) :
    IntegralMixedFramedUnitBodyBits.expression w physical key i =
      IntegralMixedFramedUnitBodyBits.expression v physical key i := by
  unfold IntegralMixedFramedUnitBodyBits.expression IntegralMixedFramedUnitBodyBits.active
    IntegralMixedFramedUnitBodyBits.reference IntegralMixedFramedUnitBodyBits.rowWord IntegralMixedFramedUnitBodyBits.field
  rw [hw]

private theorem writer_expression (key : List Bool) (physical : Bool) (i : ℕ) :
    IntegralMixedFramedUnitBodyBits.expression (writer P) physical key i =
      IntegralMixedFramedUnitBodyBits.expression (fun _ => IntegralMixedUnitRecordCode.body
        (P.ambient (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P key)) physical key i :=
  expression_congr _ _ key rfl physical i

/-- All keys, including padded integer instructions and absent records, have literal unit cells. -/
theorem unitSnapshot : IntegralMixedFramedUnitSnapshotBits.Snapshot P (plan P O hn hcap hroom)
    (data P O hn hcap hroom hSW) (writer P) where
  leading key := by rw [instruction_source P O hn hcap hroom]; rfl
  physicalScales key i := by
    change (IntegralMixedFramedPhysicalBits.rule P (plan P O hn hcap hroom) key).scales i=1
    rw [physical_rule P O hn hcap hroom]
    split_ifs <;> rfl
  virtualScales key i := by
    rw [virtual_rule P O hn hcap hroom hSW]
    rfl
  physicalHeights key i := by
    change Fin (P.ambient (pairFst key)+1) at i
    change (IntegralMixedFramedPhysicalBits.rule P (plan P O hn hcap hroom) key).heights i=_
    rw [physical_rule P O hn hcap hroom, writer_expression]
    rw [IntegralMixedUnitRecordSemantics.physical_expression _ _ _ _ _ i.isLt]
    split_ifs <;> rfl
  virtualHeights key i := by
    rw [virtual_rule P O hn hcap hroom hSW, writer_expression]
    exact (IntegralMixedUnitRecordSemantics.virtual_expression _ _ _ _ _ i.isLt).symm
  height key := by
    rw [virtual_rule P O hn hcap hroom hSW]
    unfold IntegralMixedFramedUnitBodyBits.height IntegralMixedFramedUnitBodyBits.field
    change IntegralMixedUnitRecordCode.height (P.ambient (pairFst key)) (selectedCode P key) =
      Nat.fromBitsLE (IntegralMixedFramedUnitBodyBits.field (fun _ => IntegralMixedUnitRecordCode.body
        (P.ambient (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P key)) 0 key) % _
    rw [IntegralMixedUnitRecordSemantics.decoded_height, Nat.mod_eq_of_lt
      (IntegralMixedUnitRecordCode.height_lt_arity _ (hn _) _)]
  slope key := by
    rw [virtual_rule P O hn hcap hroom hSW]
    rfl

/-- Header provenance is independent; the body and snapshot are derived from the records. -/
noncomputable def unitControls (a : Access P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P (plan P O hn hcap hroom)
      (data P O hn hcap hroom hSW) T) :
    IntegralMixedFramedUnitControlsBits.Controls P (plan P O hn hcap hroom)
      (data P O hn hcap hroom hSW) where
  tables := T
  native := ht
  represents := hr
  writer := writer P
  writer_FP := writer_FP P a
  snapshot := unitSnapshot P O hn hcap hroom hSW
end LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
