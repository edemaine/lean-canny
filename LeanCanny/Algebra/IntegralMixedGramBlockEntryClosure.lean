/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramBlockEntryNative
public import LeanCanny.Algebra.IntegralMixedGramCharacteristicBounds

/-! # The Gram determinant block entry closes against the actual row model -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramBlockEntryNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedGramBlockEntryTasks
open scoped Classical
attribute [local irreducible] IntegralMixedValueGramSumSource.value

theorem replies (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (own : IntegralMixedValueRowModel.Matches P F answer) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    RepliesAt P F answer q := by
  apply IntegralMixedValueRowInternalReplies.at_phase P F answer own _ 26 (by decide) (by decide)
  · exact IntegralMixedValueRowInternalReplies.valid_transport P q _ hv (query_root P F q) (query_birth P F q)
  · exact IntegralMixedValueFieldQuery.query_routine P (third P F) .pscEntry .companion .col (basisCol P F) q
  · exact IntegralMixedValueFieldQuery.query_phase P (third P F) .pscEntry .companion .col (basisCol P F) q

theorem correct_of_rows (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (own : IntegralMixedValueRowModel.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h answer (fun q hs => replies P F answer own q hs.1)

end LeanCanny.Algebra.IntegralMixedGramBlockEntryNative
