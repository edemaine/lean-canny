/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitData
public import LeanCanny.Algebra.IntegralMixedFramedUnitControls
/-! # Actual canonical records produce their unit snapshot -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (O : Originals P) (F : Inputs)
  (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
  (hn : ∀ root, 0<P.ambient root)
  (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
  (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root) ≤ P.width root)
  (hroom : ∀ root, count root+seedCount F root+2 ≤ P.cap root+1)
  (hSW : ∀ root, (P.degree root).size ≤ P.sourceWidth root)

private theorem expression_congr (w v : List Bool → List Bool) (key : List Bool) (hw : w key=v key)
    (physical : Bool) (i : ℕ) :
    IntegralMixedFramedUnitBodyBits.expression w physical key i =
      IntegralMixedFramedUnitBodyBits.expression v physical key i := by
  unfold IntegralMixedFramedUnitBodyBits.expression IntegralMixedFramedUnitBodyBits.active
    IntegralMixedFramedUnitBodyBits.reference IntegralMixedFramedUnitBodyBits.rowWord IntegralMixedFramedUnitBodyBits.field
  rw [hw]

private theorem writer_expression (key : List Bool) (physical : Bool) (i : ℕ) :
    IntegralMixedFramedUnitBodyBits.expression (writer P F) physical key i =
      IntegralMixedFramedUnitBodyBits.expression (fun _ => IntegralMixedUnitRecordCode.body
        (P.ambient (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P F key)) physical key i :=
  expression_congr _ _ key rfl physical i

/-- All keys, including the integer prelude and absent records, have literal unit cells. -/
theorem unitSnapshot : IntegralMixedFramedUnitSnapshotBits.Snapshot P (plan P O F C h hn hcap hW hroom)
    (data P O F C h hn hcap hW hroom hSW) (writer P F) where
  leading key := by rw [instruction_source P O F C h hn hcap hW hroom]; rfl
  physicalScales key i := by
    change (IntegralMixedFramedPhysicalBits.rule P (plan P O F C h hn hcap hW hroom) key).scales i=1
    rw [physical_rule P O F C h hn hcap hW hroom]
    split_ifs <;> rfl
  virtualScales key i := by
    rw [virtual_rule P O F C h hn hcap hW hroom hSW]
    rfl
  physicalHeights key i := by
    change Fin (P.ambient (pairFst key)+1) at i
    change (IntegralMixedFramedPhysicalBits.rule P (plan P O F C h hn hcap hW hroom) key).heights i=_
    rw [physical_rule P O F C h hn hcap hW hroom, writer_expression]
    rw [IntegralMixedUnitRecordSemantics.physical_expression _ _ _ _ _ i.isLt]
    split_ifs <;> rfl
  virtualHeights key i := by
    rw [virtual_rule P O F C h hn hcap hW hroom hSW, writer_expression]
    exact (IntegralMixedUnitRecordSemantics.virtual_expression _ _ _ _ _ i.isLt).symm
  height key := by
    rw [virtual_rule P O F C h hn hcap hW hroom hSW]
    unfold IntegralMixedFramedUnitBodyBits.height IntegralMixedFramedUnitBodyBits.field
    change IntegralMixedUnitRecordCode.height (P.ambient (pairFst key)) (selectedCode P F key) =
      Nat.fromBitsLE (IntegralMixedFramedUnitBodyBits.field (fun _ => IntegralMixedUnitRecordCode.body
        (P.ambient (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P F key)) 0 key) % _
    rw [IntegralMixedUnitRecordSemantics.decoded_height, Nat.mod_eq_of_lt
      (IntegralMixedUnitRecordCode.height_lt_arity _ (hn _) _)]
  slope key := by
    rw [virtual_rule P O F C h hn hcap hW hroom hSW]
    rfl

/-- Header provenance is independent; the body and snapshot are derived from the records. -/
noncomputable def unitControls (a : Access P) (hF : F.Access)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P (plan P O F C h hn hcap hW hroom)
      (data P O F C h hn hcap hW hroom hSW) T) :
    IntegralMixedFramedUnitControlsBits.Controls P (plan P O F C h hn hcap hW hroom)
      (data P O F C h hn hcap hW hroom hSW) where
  tables := T
  native := ht
  represents := hr
  writer := writer P F
  writer_FP := writer_FP P a hF
  snapshot := unitSnapshot P O F C h hn hcap hW hroom hSW
end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
