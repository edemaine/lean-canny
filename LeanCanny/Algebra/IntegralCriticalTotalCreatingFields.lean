/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingSource
/-! # Native scalar metadata of the total creating source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandObjective (F : Scripts) (q : List Bool) : ℕ :=
  ((IntegralCriticalScriptFP.commandAt (IntegralCriticalFlatClearedHeightBits.metadata F) q
    (IntegralCriticalHistoryTask.birth F.toParameters q)).map Command.objective).getD 0
noncomputable def commandCoordinate (F : Scripts) (q : List Bool) : ℕ :=
  ((IntegralCriticalScriptFP.commandAt (IntegralCriticalFlatClearedHeightBits.metadata F) q
    (IntegralCriticalHistoryTask.birth F.toParameters q)).map Command.coordinate).getD 0

theorem at_ambient (F : Scripts) (q : List Bool) :
    (atFamily F q).ambient [] + 1 = if valid F q then F.ambient (root q) + 1 else 1 := by
  by_cases h : valid F q
  · rw [atFamily_valid F q h, ite_eq_left h]; rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]; rfl

theorem at_rank (F : Scripts) (q : List Bool) : rank F q = if valid F q then oldRank F q else 1 := by
  unfold rank
  by_cases h : valid F q
  · rw [atFamily_valid F q h, creating_birth F q h, ite_eq_left h]; rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]; rfl

theorem at_offset (F : Scripts) (q : List Bool) :
    (atFamily F q).offset [] = if valid F q then commandOffset F q else 0 := by
  by_cases h : valid F q
  · rw [atFamily_valid F q h, ite_eq_left h, commandOffset_creating F q h]; rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]; rfl

theorem at_free (F : Scripts) (q : List Bool) :
    (atFamily F q).free [] + 1 = if valid F q then F.ambient (root q) - commandOffset F q + 1 else 1 := by
  by_cases h : valid F q
  · rw [atFamily_valid F q h, ite_eq_left h, commandOffset_creating F q h]; rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]; rfl

theorem at_sourceWidth (F : Scripts) (q : List Bool) :
    (atFamily F q).sourceWidth [] = if valid F q then F.sourceWidth (root q) else 2 := by
  by_cases h : valid F q
  · rw [atFamily_valid F q h, ite_eq_left h]; rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]; rfl

theorem at_degree (F : Scripts) (q : List Bool) :
    ((atFamily F q).data []).degree = if valid F q then commandDegree F q else 2 := by
  by_cases h : valid F q
  · rw [atFamily_valid F q h, ite_eq_left h, commandDegree_creating F q h]; rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]; rfl

theorem commandObjective_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    commandObjective F q = (chosen (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h)).objective := by
  unfold commandObjective
  rw [commandAt_creating F q h]
  rfl

theorem commandCoordinate_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    commandCoordinate F q = (chosen (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h)).coordinate := by
  unfold commandCoordinate
  rw [commandAt_creating F q h]
  rfl

theorem at_objective (F : Scripts) (q : List Bool) :
    ((atFamily F q).objective []).val = if valid F q then commandObjective F q % ((atFamily F q).free [] + 1) else 0 := by
  by_cases h : valid F q
  · rw [ite_eq_left h, commandObjective_creating F q h, atFamily_valid F q h]; rfl
  · rw [ite_eq_right h, atFamily_invalid F q h]; rfl

theorem at_coordinate (F : Scripts) (q : List Bool) :
    ((atFamily F q).coordinate []).val = if valid F q then commandCoordinate F q % ((atFamily F q).free [] + 1) else 0 := by
  by_cases h : valid F q
  · rw [ite_eq_left h, commandCoordinate_creating F q h, atFamily_valid F q h]; rfl
  · rw [ite_eq_right h, atFamily_invalid F q h]; rfl

attribute [local irreducible] atFamily

theorem arity_unary (F : Scripts) (a : Access F) : UnaryFn (euler F).arity :=
  (UnaryFn.ite (valid_FP F a) ((a.ambient.comp RankedHistoryTask.root_FP).add (UnaryFn.const 1)) (UnaryFn.const 1)).of_eq
    (fun q => (at_ambient F q).symm)

theorem rank_binary (F : Scripts) (a : Access F) : BinaryFn (euler F).rank :=
  (BinaryFn.ite (valid_FP F a) (oldRank_binary F a) (BinaryFn.const 1)).of_eq
    (fun q => (at_rank F q).symm)

theorem offset_unary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : UnaryFn (euler F).offset :=
  (UnaryFn.ite (valid_FP F a) (commandOffset_unary F a n) (UnaryFn.const 0)).of_eq
    (fun q => (at_offset F q).symm)

theorem free_unary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : UnaryFn (euler F).free :=
  (UnaryFn.ite (valid_FP F a)
    (((a.ambient.comp RankedHistoryTask.root_FP).sub (commandOffset_unary F a n)).add (UnaryFn.const 1)) (UnaryFn.const 1)).of_eq
    (fun q => (at_free F q).symm)

theorem sourceWidth_unary (F : Scripts) (a : Access F) : UnaryFn (euler F).sourceWidth :=
  (UnaryFn.ite (valid_FP F a) (a.sourceWidth.comp RankedHistoryTask.root_FP) (UnaryFn.const 2)).of_eq
    (fun q => (at_sourceWidth F q).symm)

theorem degree_binary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : BinaryFn (euler F).degree :=
  (BinaryFn.ite (valid_FP F a) (commandDegree_binary F a n) (BinaryFn.const 2)).of_eq
    (fun q => (at_degree F q).symm)

theorem targetWidth_unary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : UnaryFn (euler F).targetWidth :=
  PurePowerReductionBounds.width_unary (free_unary F a n) (degree_binary F a n)

theorem objective_binary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) (ho : BinaryFn (commandObjective F)) :
    BinaryFn (fun q => ((euler F).objective q).val) :=
  (BinaryFn.ite (valid_FP F a) (ho.mod (BinaryFn.ofUnary (free_unary F a n))) (BinaryFn.const 0)).of_eq
    (fun q => (at_objective F q).symm)

theorem coordinate_binary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) (hc : BinaryFn (commandCoordinate F)) :
    BinaryFn (fun q => ((source F).coordinate q).val) :=
  (BinaryFn.ite (valid_FP F a) (hc.mod (BinaryFn.ofUnary (free_unary F a n))) (BinaryFn.const 0)).of_eq
    (fun q => (at_coordinate F q).symm)
end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
