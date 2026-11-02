/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitBody
/-! # Literal unit-selector snapshots at each creating source record

The hypotheses identify original syntax, never an interpreted bank reader.
Every key includes its saved birth; no root-only source substitution occurs.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedHistory
open IntegralMixedFramedScalarCellsBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Snapshot (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) : Prop where
  leading : ∀ key, (IntegralMixedFramedHistoryFamilyBits.instruction P D key).source.leading = 1
  physicalScales : ∀ key i, ((physicalFamily P D H).rule key).scales i = 1
  virtualScales : ∀ key i, (((virtualFamily P D H).rule key).critical).scales i = 1
  physicalHeights : ∀ key i, ((physicalFamily P D H).rule key).heights i =
    IntegralMixedFramedUnitBodyBits.expression writer true key i.val
  virtualHeights : ∀ key i, (((virtualFamily P D H).rule key).critical).heights i =
    IntegralMixedFramedUnitBodyBits.expression writer false key i.val
  height : ∀ key, ((virtualFamily P D H).rule key).height.val = IntegralMixedFramedUnitBodyBits.height P writer key
  slope : ∀ key, ((virtualFamily P D H).rule key).slope = 1

noncomputable def physical (key : List Bool) : Bool := decide (IntegralMixedHeightCellsBits.context key = 1)

noncomputable def selectedExpression (writer : List Bool → List Bool) (key : List Bool) (i : ℕ) :=
  IntegralMixedFramedUnitBodyBits.expression writer (physical key) key i

noncomputable def active (P : Parameters) (writer : List Bool → List Bool) (q : List Bool) : Prop :=
  get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1 ∧
    IntegralMixedFramedUnitBodyBits.active writer (physical (IntegralMixedVirtualTaskBits.saved P q))
      (IntegralMixedVirtualTaskBits.saved P q) (get P .slot8 q) = true

noncomputable def reference (P : Parameters) (writer : List Bool → List Bool) (q : List Bool) :=
  IntegralMixedFramedUnitBodyBits.reference writer (physical (IntegralMixedVirtualTaskBits.saved P q))
    (IntegralMixedVirtualTaskBits.saved P q) (get P .slot8 q)

theorem rule_height (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (key : List Bool)
    (i : Fin (P.ambient (pairFst key) + 1)) :
    (rule P D H key).heights i = selectedExpression writer key i.val := by
  unfold rule selectedExpression physical
  by_cases hc : IntegralMixedHeightCellsBits.context key = 1
  · rw [ite_eq_left hc, decide_eq_true hc]
    exact h.physicalHeights key i
  · rw [ite_eq_right hc, decide_eq_false hc]
    exact h.virtualHeights key i

theorem rule_scale (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (key : List Bool)
    (i : Fin (P.ambient (pairFst key) + 1)) : (rule P D H key).scales i = 1 := by
  unfold rule
  split_ifs
  · exact h.physicalScales key i
  · exact h.virtualScales key i

theorem affine_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) :
    affine P D H q = if active P writer q then .reference (reference P writer q) else .constant 0 := by
  unfold affine active reference
  by_cases hi : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1
  · rw [dite_eq_left hi, rule_height P D H writer h]
    simp only [hi, true_and, selectedExpression, IntegralMixedFramedUnitBodyBits.expression]
  · rw [dite_eq_right hi]
    simp only [hi, false_and, ite_false]

theorem constant_zero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) :
    IntegralMixedAffineCoefficients.constantCoefficient (affine P D H q) = 0 := by
  rw [affine_eq P D H writer h]
  split_ifs <;> rfl

theorem reference_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) (i : ℕ) :
    IntegralMixedAffineCoefficients.referenceCoefficient (affine P D H q) i =
      if active P writer q ∧ reference P writer q = i then 1 else 0 := by
  rw [affine_eq P D H writer h]
  by_cases ha : active P writer q
  · rw [ite_eq_left ha]
    simp only [IntegralMixedAffineCoefficients.referenceCoefficient, ha, true_and]
  · rw [ite_eq_right ha]
    simp only [IntegralMixedAffineCoefficients.referenceCoefficient, ha, false_and, ite_false]

theorem cell_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) (tag i : ℕ) :
    cell P D H q tag i =
      if tag = 1 then (if active P writer q ∧ reference P writer q = i then 1 else 0)
      else if tag = 2 then 1
      else if tag = 3 then (if get P .slot8 q = IntegralMixedFramedUnitBodyBits.height P writer (IntegralMixedVirtualTaskBits.saved P q) then 1 else 0)
      else 0 := by
  unfold cell
  by_cases h0 : tag = 0
  · subst tag
    simp only [ite_true, constant_zero P D H writer h, show (0 : ℕ) ≠ 1 by decide, show (0 : ℕ) ≠ 2 by decide, show (0 : ℕ) ≠ 3 by decide, ite_false]
  · rw [ite_eq_right h0]
    by_cases h1 : tag = 1
    · rw [ite_eq_left h1, ite_eq_left h1, reference_eq P D H writer h]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : tag = 2
      · rw [ite_eq_left h2, ite_eq_left h2]
        split_ifs
        · exact rule_scale P D H writer h _ _
        · rfl
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : tag = 3
        · rw [ite_eq_left h3, ite_eq_left h3, h.height, h.slope]
        · rw [ite_eq_right h3, ite_eq_right h3]

theorem leading_one (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) : leading P D q = 1 :=
  h.leading _
end LeanCanny.Algebra.IntegralMixedFramedUnitSnapshotBits
