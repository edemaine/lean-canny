/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueRowBoundaryReplies

/-! # Actual row dispatcher correctness with all internal replies closed -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowDispatcher
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (answer : List Bool → List Bool) (he : IntegralMixedValueRowBoundaryReplies.External P F answer)
    (own : IntegralMixedValueRowModel.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  have H21 := IntegralMixedFullRowBranch.correct P a F h g answer
    (fun q hs => IntegralMixedValueRowBoundaryReplies.fullrow P F answer he q hs.1)
  have H22 := IntegralMixedValueHomogeneousBranch.correct P a F h g answer
    (fun q hs => IntegralMixedValueRowBoundaryReplies.homogeneous P F answer he own q hs.1)
  have H23 := IntegralMixedValueReciprocalBranch.correct P a F h answer
    (fun q hs => IntegralMixedValueRowInternalReplies.reciprocal P F answer own q hs.1)
  have H24 := IntegralMixedValueMacaulayBranch.correct P a F h g answer
    (fun q hs => IntegralMixedValueRowInternalReplies.macaulay P F answer own q hs.1)
  have H25 := IntegralMixedValueGramProductNative.correct P a F h answer
    (fun q hs => IntegralMixedValueRowInternalReplies.product P F answer own q hs.1)
  have H26 := IntegralMixedValueGramSumNative.correct P a F h g answer
    (fun q hs => IntegralMixedValueRowInternalReplies.sum P F answer own q hs.1)
  unfold machine
  apply choose_correct _ _ _ _ H21
  apply choose_correct _ _ _ _ H22
  apply choose_correct _ _ _ _ H23
  apply choose_correct _ _ _ _ H24
  apply choose_correct _ _ _ _ H25
  apply choose_correct _ _ _ _ H26
  exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedValueRowDispatcher
