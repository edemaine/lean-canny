/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerDefault
/-! # One producer value agrees with the literal creating command in every context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  if get P .slot15 q = 0 then IntegralMixedIntegerProducerBits.leadingValue P D q
  else if get P .slot15 q = 1 then IntegralMixedPhysicalProducerLeadingBits.value P (IntegralMixedPhysicalCompanionBits.fullFamily P D) q
  else IntegralMixedNormalizationTopBits.leadingValue P (IntegralMixedNormalizedCompanionBits.fullFamily P D) q

noncomputable def companion (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  if get P .slot15 q = 0 then IntegralMixedIntegerProducerBits.companionValue P D q
  else if get P .slot15 q = 1 then IntegralMixedPhysicalCompanionBits.companionValue P (IntegralMixedPhysicalCompanionBits.fullFamily P D) q
  else IntegralMixedNormalizedCompanionBits.companionValue P (IntegralMixedNormalizedCompanionBits.fullFamily P D) q

theorem leading_actual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hctx : get P .slot15 q = (IntegralMixedFullHistoryFamilyBits.creatingCommand P D (IntegralMixedVirtualTaskBits.saved P q)).context) :
    leading P D q = residueBits (IntegralMixedFullHistoryCompanionBits.leading P D (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  cases hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) with
  | none =>
    have hx : get P .slot15 q = 0 := by
      simpa only [IntegralMixedFullHistoryFamilyBits.creatingCommand, hc, Option.getD_none, defaultCommand, Command.context] using hctx
    rw [leading, ite_eq_left hx]
    exact IntegralMixedIntegerProducerBits.leading_default P D q hc
  | some c =>
    have hx : get P .slot15 q = c.context := by
      simpa only [IntegralMixedFullHistoryFamilyBits.creatingCommand, hc, Option.getD_some] using hctx
    cases c with
    | integer p hp hd =>
      rw [leading, hx, Command.context, ite_eq_left rfl]
      exact IntegralMixedFullHistoryCompanionBits.integer_leading P D q p hp hd hc
    | critical r =>
      rw [leading, hx, Command.context, ite_eq_right (by decide), ite_eq_left rfl]
      exact IntegralMixedFullHistoryCompanionBits.physical_leading P D q r hc
    | cut r k d ha hd =>
      have hn0 : Command.context (.cut r k d ha hd) ≠ 0 := by cases k <;> norm_num [Command.context]
      have hn1 : Command.context (.cut r k d ha hd) ≠ 1 := by cases k <;> norm_num [Command.context]
      rw [leading, hx, ite_eq_right hn0, ite_eq_right hn1]
      exact IntegralMixedFullHistoryCompanionBits.normalized_leading P D q r k d ha hd hc

theorem companion_actual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hctx : get P .slot15 q = (IntegralMixedFullHistoryFamilyBits.creatingCommand P D (IntegralMixedVirtualTaskBits.saved P q)).context)
    (hcoord : get P .slot13 q = (IntegralMixedFullHistoryFamilyBits.creatingCommand P D (IntegralMixedVirtualTaskBits.saved P q)).coordinate) :
    companion P D q = IntegralMixedFullHistoryCompanionBits.value P D q := by
  cases hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) with
  | none =>
    have hx : get P .slot15 q = 0 := by
      simpa only [IntegralMixedFullHistoryFamilyBits.creatingCommand, hc, Option.getD_none, defaultCommand, Command.context] using hctx
    rw [companion, ite_eq_left hx]
    exact IntegralMixedIntegerProducerBits.value_default P D q hc
  | some c =>
    have hx : get P .slot15 q = c.context := by
      simpa only [IntegralMixedFullHistoryFamilyBits.creatingCommand, hc, Option.getD_some] using hctx
    have hy : get P .slot13 q = c.coordinate := by
      simpa only [IntegralMixedFullHistoryFamilyBits.creatingCommand, hc, Option.getD_some] using hcoord
    cases c with
    | integer p hp hd =>
      rw [companion, hx, Command.context, ite_eq_left rfl]
      exact IntegralMixedIntegerProducerBits.value_creating P D q p hp hd hc
    | critical r =>
      rw [companion, hx, Command.context, ite_eq_right (by decide), ite_eq_left rfl]
      exact IntegralMixedPhysicalCompanionBits.value_creating P D q r hc hy
    | cut r k d ha hd =>
      have hn0 : Command.context (.cut r k d ha hd) ≠ 0 := by cases k <;> norm_num [Command.context]
      have hn1 : Command.context (.cut r k d ha hd) ≠ 1 := by cases k <;> norm_num [Command.context]
      rw [companion, hx, ite_eq_right hn0, ite_eq_right hn1]
      exact IntegralMixedNormalizedCompanionBits.value_creating P D q r k d ha hd hc

end LeanCanny.Algebra.IntegralMixedProducerActualBits
