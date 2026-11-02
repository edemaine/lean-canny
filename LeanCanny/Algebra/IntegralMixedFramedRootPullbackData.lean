/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction

/-! # Literal fallback data transported with the creating instruction

The projected instruction supplies the same source and fallback selection.
Dependent selection transport preserves its complete header and sweep rule;
no polynomial is reconstructed from encoded metadata.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open scoped Classical

noncomputable def data (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) :
    IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra) where
  degree_eq q := (instruction_degree P D project extra q).trans
    ((H.degree_eq (key project q)).trans (congrArg P.degree (key_root project q)))
  sourceWidth q := by
    exact ((H.sourceWidth (key project q)).trans_eq (congrArg P.sourceWidth (key_root project q))).trans_eq'
      (congrArg Nat.size (instruction_degree P D project extra q)).symm
  fallback q := transportSelection (congrArg P.ambient (key_root project q).symm)
    (instruction_source P D project extra q) (H.fallback (key project q))

theorem fallback_header (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (q : List Bool) :
    IntegralMixedCommandHeaderBits.selection ((data P D H project extra).fallback q)=
      IntegralMixedCommandHeaderBits.selection (H.fallback (key project q)) :=
  transportSelection_header _ _ _

noncomputable def selectAt {n B : ℕ} (I : Instruction n B)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection I.source) :
    IntegralMixedFullHistoryFamilyBits.Selection I.source :=
  match I.command with
  | .cut r k d hd _ => ⟨r,k,d,hd⟩
  | _ => fallback

theorem selection_selectAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.selection P D H q=
      selectAt (IntegralMixedFramedHistoryFamilyBits.instruction P D q) (H.fallback q) := by
  unfold IntegralMixedFramedHistoryFamilyBits.selection selectAt
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D q).command <;> rfl

theorem selection_rule_heq {n n' B B' : ℕ} (I : Instruction n B) (J : Instruction n' B')
    (hn : n=n') (hB : B=B') (hI : HEq I J) (hS : HEq I.source J.source)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection J.source) :
    HEq (selectAt I (transportSelection hn hS fallback)).rule (selectAt J fallback).rule := by
  cases hn
  cases hB
  have H : I=J := eq_of_heq hI
  cases H
  rfl

theorem virtual_rule_heq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (q : List Bool) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family (parameters P project extra) (plan P D project extra)
      (data P D H project extra)).rule q)
      ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule (key project q)) := by
  have HS := selection_rule_heq _ _ (congrArg P.ambient (key_root project q).symm)
    (congrArg P.width (key_root project q).symm) (instruction_heq P D project extra q)
    (instruction_source P D project extra q) (H.fallback (key project q))
  have HN := congrArg (fun s=>s.rule) (selection_selectAt (parameters P project extra) (plan P D project extra) (data P D H project extra) q)
  have HO := congrArg (fun s=>s.rule) (selection_selectAt P D H (key project q))
  exact (heq_of_eq HN).trans (HS.trans (heq_of_eq HO.symm))

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
