/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackHeaders
public import LeanCanny.Algebra.IntegralMixedFramedUnitControls

/-! # Literal unit-selector snapshots preserve root, birth and context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open scoped Classical

noncomputable def physicalAt {n B : ℕ} (I : Instruction n B) : CriticalRule n :=
  match I.command with
  | .critical r => r
  | _ => IntegralMixedFullPhysicalBits.defaultRule n

theorem physicalAt_eq (P : Parameters) (D : Plan P) (q : List Bool) :
    IntegralMixedFramedPhysicalBits.rule P D q=physicalAt (IntegralMixedFramedHistoryFamilyBits.instruction P D q) := by
  unfold IntegralMixedFramedPhysicalBits.rule physicalAt
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D q).command <;> rfl

theorem physical_rule_heq (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedPhysicalBits.rule (parameters P project extra) (plan P D project extra) q)
      (IntegralMixedFramedPhysicalBits.rule P D (key project q)) := by
  have HS := instruction_read_heq (fun _ _ I=>physicalAt I) _ _
    (congrArg P.ambient (key_root project q).symm) (congrArg P.width (key_root project q).symm)
    (instruction_heq P D project extra q)
  exact (heq_of_eq (physicalAt_eq _ _ _)).trans (HS.trans (heq_of_eq (physicalAt_eq P D _).symm))

theorem critical_pred {n m : ℕ} (f : ∀ n,CriticalRule n→Prop) (r : CriticalRule n) (s : CriticalRule m)
    (hn : n=m) (h : HEq r s) (hs : f m s) : f n r := by
  cases hn
  have H : r=s := eq_of_heq h
  cases H
  exact hs

theorem sweep_pred {n m : ℕ} (f : ∀ n,IntegralMixedCriticalSweep.Rule n→Prop)
    (r : IntegralMixedCriticalSweep.Rule n) (s : IntegralMixedCriticalSweep.Rule m)
    (hn : n=m) (h : HEq r s) (hs : f m s) : f n r := by
  cases hn
  have H : r=s := eq_of_heq h
  cases H
  exact hs

theorem sweep_read {α : Type} {n m : ℕ} (f : ∀ n,IntegralMixedCriticalSweep.Rule n→α)
    (r : IntegralMixedCriticalSweep.Rule n) (s : IntegralMixedCriticalSweep.Rule m)
    (hn : n=m) (h : HEq r s) : f n r=f m s := by
  cases hn
  have H : r=s := eq_of_heq h
  cases H
  rfl

theorem body_height_key (P : Parameters) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (writer : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedUnitBodyBits.height (parameters P project extra) (writer ∘ key project) q=
      IntegralMixedFramedUnitBodyBits.height P writer (key project q) := by
  simp only [IntegralMixedFramedUnitBodyBits.height,IntegralMixedFramedUnitBodyBits.field,
    parameters,Function.comp_apply,key_root]

theorem snapshot (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool→List Bool) (h : IntegralMixedFramedUnitSnapshotBits.Snapshot P D H writer)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) :
    IntegralMixedFramedUnitSnapshotBits.Snapshot (parameters P project extra) (plan P D project extra)
      (data P D H project extra) (writer ∘ key project) where
  leading q := (instruction_leading P D project extra q).trans (h.leading (key project q))
  physicalScales q := critical_pred (fun _ r=>∀ i,r.scales i=1) _ _
    (congrArg P.ambient (key_root project q).symm) (physical_rule_heq P D project extra q) (h.physicalScales _)
  virtualScales q := sweep_pred (fun _ r=>∀ i,r.critical.scales i=1) _ _
    (congrArg P.ambient (key_root project q).symm) (virtual_rule_heq P D H project extra q) (h.virtualScales _)
  physicalHeights q := critical_pred
    (fun _ r=>∀ i,r.heights i=IntegralMixedFramedUnitBodyBits.expression writer true (key project q) i.val) _ _
    (congrArg P.ambient (key_root project q).symm) (physical_rule_heq P D project extra q) (h.physicalHeights _)
  virtualHeights q := sweep_pred
    (fun _ r=>∀ i,r.critical.heights i=IntegralMixedFramedUnitBodyBits.expression writer false (key project q) i.val) _ _
    (congrArg P.ambient (key_root project q).symm) (virtual_rule_heq P D H project extra q) (h.virtualHeights _)
  height q := (sweep_read (fun _ r=>r.height.val) _ _ (congrArg P.ambient (key_root project q).symm)
    (virtual_rule_heq P D H project extra q)).trans ((h.height _).trans (body_height_key P project extra writer q).symm)
  slope q := (sweep_read (fun _ r=>r.slope) _ _ (congrArg P.ambient (key_root project q).symm)
    (virtual_rule_heq P D H project extra q)).trans (h.slope _)

noncomputable def unit (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedUnitControlsBits.Controls P D H) (project : List Bool→List Bool) (hp : project∈FP)
    (extra : List Bool→ℕ) :
    IntegralMixedFramedUnitControlsBits.Controls (parameters P project extra) (plan P D project extra) (data P D H project extra) where
  tables := tables h.tables project
  native := tablesAccess h.tables h.native project hp
  represents := represents P D H h.tables h.represents project extra
  writer := h.writer ∘ key project
  writer_FP := mem_FP_comp (key_FP project hp) h.writer_FP
  snapshot := snapshot P D H h.writer h.snapshot project extra

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
