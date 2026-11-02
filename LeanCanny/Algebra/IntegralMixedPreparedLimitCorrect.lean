/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPreparedLimitNative
/-! # The prepared native limit branch returns the actual truncated cut source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPreparedLimitNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical
attribute [local irreducible] IntegralMixedRawKindBits.prepare IntegralMixedNormalizationTopBits.rawCutValue

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R)
    (answer : List Bool → List Bool) (critical : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (bank : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedOldBankCofactorBits.RepliesAt P F R answer q) :
    Correct (machine P a F h k hd R hr) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply NativePreparedBranch.correct
  · exact IntegralMixedLimitCoordinateNative.branch_correct P a F h g R hr answer critical (fun q hs => bank q hs.1)
  · intro q _
    exact kernel_selected P a F h R hr q
  · intro q hq
    exact kernel_value P a F h g R hr q (of_decide_eq_true hq)
  · intro q child hq hc
    have hs : Selected P F q := of_decide_eq_true hq
    exact IntegralMixedRawKindBits.prepare_frame P F q child hs.2.1 hs.2.2.1 hc

end LeanCanny.Algebra.IntegralMixedPreparedLimitNative
