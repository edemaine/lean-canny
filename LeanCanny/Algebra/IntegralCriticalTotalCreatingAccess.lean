/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingFields
public import LeanCanny.Algebra.IntegralEulerSemanticAccess
/-! # One native access record for the total creating Euler source

The native controls use scalar command fields only. The coefficient and
height readers are actual semantic leaves; no complexity certificate for
either reader is assumed here.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] atFamily residueBits

theorem controls (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) : IntegralEulerSemanticBits.Controls (euler F) where
  arity := arity_unary F a
  free := free_unary F a n
  offset := offset_unary F a n
  sourceWidth := sourceWidth_unary F a
  targetWidth := targetWidth_unary F a n
  rank := rank_binary F a
  allowance := degree_binary F a n
  target := IntegralCriticalHistoryTask.get_binary _ a.toAccess .target
  row := (IntegralCriticalHistoryTask.get_binary _ a.toAccess .row).mod (rank_binary F a)
  col := (IntegralCriticalHistoryTask.get_binary _ a.toAccess .col).mod (rank_binary F a)
  modulus := IntegralCriticalHistoryTask.modulus_binary _ a.toAccess
  degree := degree_binary F a n
  objective := objective_binary F a n ho

noncomputable def access (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) : IntegralEulerBits.Access (euler F) :=
  IntegralEulerSemanticBits.access (euler F) (controls F a n ho)

noncomputable def criticalAccess (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) (hc : BinaryFn (commandCoordinate F)) : IntegralClearedCriticalBits.Access (source F) where
  toEuler := IntegralCriticalTotalCreatingBits.access F a n ho
  bound := PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary (free_unary F a n)) (degree_binary F a n)
  coordinate := coordinate_binary F a n hc
  coefficientIndex := IntegralCriticalHistoryTask.get_binary _ a.toAccess .coefficient
end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
