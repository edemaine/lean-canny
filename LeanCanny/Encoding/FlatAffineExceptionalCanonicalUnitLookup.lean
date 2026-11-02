/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
/-! # Exact chronological source selection of the concrete canonical plan -/
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

noncomputable def prelude (root : List Bool) :=
  FlatAffineExceptionalFramedIntegerPrelude.commands (source P O root 0) (P.width root)
    ((by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
      PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root) ≤
        IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (hcap root))
    F C h (input root) (hW root)

theorem prelude_length (root : List Bool) : (prelude P O F C h hcap hW root).length=seedCount F root :=
  FlatAffineExceptionalFramedIntegerPrelude.length_commands _ _ _ _ _ _ _ _

theorem rules_eq (root : List Bool) :
    (plan P O F C h hn hcap hW hroom).rules root = later P O F hn hcap root ++ prelude P O F C h hcap hW root := rfl

private theorem reverse_lookup_append {α : Type} (xs ys : List α) (b : ℕ) :
    (xs++ys).reverse[b]? = if b<ys.length then ys.reverse[b]? else xs.reverse[b-ys.length]? := by
  rw [List.reverse_append]
  by_cases hb : b<ys.length
  · rw [ite_eq_left hb, List.getElem?_append_left (by simpa only [List.length_reverse] using hb)]
  · rw [ite_eq_right hb, List.getElem?_append_right (by simpa only [List.length_reverse] using Nat.le_of_not_gt hb), List.length_reverse]

theorem chronological_plan (root : List Bool) (b : ℕ) :
    chronological ((plan P O F C h hn hcap hW hroom).rules root) b =
      if b<seedCount F root then chronological (prelude P O F C h hcap hW root) b
      else chronological (later P O F hn hcap root) (b-seedCount F root) := by
  rw [rules_eq]
  unfold chronological
  rw [reverse_lookup_append, prelude_length]

theorem instruction_later (key : List Bool) (hl : inLater P F key) :
    IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key =
      step P O F hn hcap (pairFst key)
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key)) := by
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [chronological_plan, ite_eq_right (not_lt.mpr hl.1), later_chronological, dite_eq_left hl.2]
  rfl

theorem instruction_prefix (key : List Bool)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<seedCount F (pairFst key)) :
    IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key =
      FlatAffineExceptionalFramedIntegerPrelude.command (source P O (pairFst key) 0) (P.width (pairFst key))
        ((by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
          PurePowerReductionBounds.dimension (P.ambient (pairFst key)+1) (P.degree (pairFst key)) ≤
            IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) (P.degree (pairFst key))).trans (hcap (pairFst key)))
        F C h (input (pairFst key)) (hW (pairFst key))
        (FlatAffineExceptionalIntegerCommands.index F (input (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) hb) := by
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [chronological_plan, ite_eq_left hb]
  unfold prelude
  rw [FlatAffineExceptionalFramedIntegerPrelude.chronological_commands _ _ _ _ _ _ _ _ _ hb]
  rfl

theorem instruction_default (key : List Bool)
    (hb : seedCount F (pairFst key) ≤ IntegralMixedFramedHistoryFamilyBits.prefixLength P key)
    (hl : ¬inLater P F key) :
    IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key =
      IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (plan P O F C h hn hcap hW hroom) (pairFst key) := by
  have HN : ¬IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key)<count (pairFst key) := fun ht => hl ⟨hb, ht⟩
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [chronological_plan, ite_eq_right (not_lt.mpr hb), later_chronological, dite_eq_right HN]
  rfl

noncomputable def sourceIndex (key : List Bool) := if inLater P F key then IntegralMixedFramedHistoryFamilyBits.prefixLength P key else 0

theorem sourceIndex_binary (a : Access P) (hF : F.Access) : BinaryFn (sourceIndex P F) := by
  have HB : UnaryFn (fun key => seedCount F (pairFst key)) := (seedCount_unary hF).comp pairFst_mem_FP
  have HP : UnaryFn (IntegralMixedFramedHistoryFamilyBits.prefixLength P) := IntegralMixedFullHistoryFamilyBits.prefix_unary P a
  have HN : UnaryFn (fun key => count (pairFst key)) := count_unary.comp pairFst_mem_FP
  have HI : BinaryFn (fun key => IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key)) :=
    (BinaryFn.ofUnary HP).sub (BinaryFn.ofUnary HB)
  have HS : FPPred (inLater P F) := (FPPred.le HB HP).and (HI.lt (BinaryFn.ofUnary HN))
  exact BinaryFn.ite HS (BinaryFn.ofUnary HP) (BinaryFn.const 0)

theorem instruction_source (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key).source =
      source P O (pairFst key) (sourceIndex P F key) := by
  by_cases hl : inLater P F key
  · rw [instruction_later P O F C h hn hcap hW hroom key hl, sourceIndex, ite_eq_left hl]
    unfold step
    exact congrArg (source P O (pairFst key)) (Nat.add_sub_of_le hl.1)
  · rw [sourceIndex, ite_eq_right hl]
    by_cases hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<seedCount F (pairFst key)
    · rw [instruction_prefix P O F C h hn hcap hW hroom key hb]
      rfl
    · rw [instruction_default P O F C h hn hcap hW hroom key (Nat.le_of_not_gt hb) hl]
      rfl
end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
