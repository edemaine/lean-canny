/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
/-! # All-input selected-rule provenance of the supplied-mask history -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineExceptionalSuppliedRules (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def IsInteger {n B : ℕ} {P : SpatialSource n} : Command P B → Prop
  | .integer .. => True
  | _ => False

structure Description (P : Parameters) (F : Inputs) where
  source : Source F
  cone : FlatAffinePowerPositive.ConeCertificate (next F)
  base : IntegralMixedFullHistoryFamilyBits.Data (parameters P source)
  kind : (root : List Bool) → IntegralMixedRelativeCuts.Kind (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep source cone root)
  degree : List Bool → ℕ
  degree_bound : ∀ root, degree root ≤ IntegralMixedExceptionalBounds.auxiliaryCap ((parameters P source).ambient root + 1) (base.spatial root).degree
  room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1
  integers : ∀ root c, c ∈ base.rules root → IsInteger c

noncomputable abbrev backend (P : Parameters) {F : Inputs} (D : Description P F) :=
  data P D.source D.cone D.base D.kind D.degree D.degree_bound D.room

noncomputable abbrev chosen (P : Parameters) {F : Inputs} (D : Description P F) (root : List Bool) :=
  selection P D.source D.cone D.base D.kind D.degree D.degree_bound root

theorem base_creating_integer (P : Parameters) {F : Inputs} (D : Description P F) (key : List Bool)
    (c : Command (D.base.spatial (pairFst key)) ((parameters P D.source).width (pairFst key)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating (parameters P D.source) D.base key = some c) : IsInteger c :=
  D.integers _ c (List.mem_reverse.mp (List.mem_of_getElem? hc))

theorem selection_backend (P : Parameters) {F : Inputs} (D : Description P F) (key : List Bool) :
    IntegralMixedFullHistoryFamilyBits.selection (parameters P D.source) (backend P D) key = chosen P D (pairFst key) := by
  unfold IntegralMixedFullHistoryFamilyBits.selection
  rw [creating_eq P D.source D.cone D.base D.kind D.degree D.degree_bound D.room key]
  split_ifs
  · cases hc : IntegralMixedFullHistoryFamilyBits.creating (parameters P D.source) D.base key with
    | none => rfl
    | some c =>
      have HI := base_creating_integer P D key c hc
      cases c with
      | integer => rfl
      | critical => cases HI
      | cut => cases HI
  · rfl
  · rfl
  · rfl

theorem virtual_rule_backend (P : Parameters) {F : Inputs} (D : Description P F) (key : List Bool) :
    (IntegralMixedFullHistoryFamilyBits.family (parameters P D.source) (backend P D)).rule key =
      FlatAffineExceptionalSuppliedRules.sweep D.source D.cone (pairFst key) := by
  change (IntegralMixedFullHistoryFamilyBits.selection (parameters P D.source) (backend P D) key).rule = _
  rw [selection_backend]
  rfl

theorem physical_rule_backend (P : Parameters) {F : Inputs} (D : Description P F) (key : List Bool) :
    (IntegralMixedHeightCellsBits.physicalFamily (parameters P D.source) (backend P D)).rule key =
      if IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P D.source) key = (D.base.rules (pairFst key)).length then
        FlatAffineExceptionalSuppliedRules.coarse D.source (pairFst key)
      else IntegralMixedFullPhysicalBits.defaultRule ((parameters P D.source).ambient (pairFst key)) := by
  change IntegralMixedFullPhysicalBits.rule (parameters P D.source)
    (IntegralMixedFullHistoryFamilyBits.physicalData (parameters P D.source) (backend P D)) key = _
  rw [IntegralMixedFullPhysicalBits.rule, IntegralMixedFullHistoryFamilyBits.physical_creating,
    creating_eq P D.source D.cone D.base D.kind D.degree D.degree_bound D.room key]
  by_cases hb : IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P D.source) key < (D.base.rules (pairFst key)).length
  · rw [ite_eq_left hb, ite_eq_right (by omega)]
    cases hc : IntegralMixedFullHistoryFamilyBits.creating (parameters P D.source) D.base key with
    | none => rfl
    | some c =>
      have HI := base_creating_integer P D key c hc
      cases c with
      | integer => rfl
      | critical => cases HI
      | cut => cases HI
  · rw [ite_eq_right hb]
    split_ifs <;> rfl

end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
