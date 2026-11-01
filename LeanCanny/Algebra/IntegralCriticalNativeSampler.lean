/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeDispatcher
public import LeanCanny.Algebra.IntegralCriticalActualEntry
/-! # Actual creating companions have a native polynomial-space reader -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeSamplerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

theorem companion_evaluator (F : Scripts) (h : Controls F)
    (a : IntegralCriticalNativeLowerDispatcherBits.Primitive F) :
    SpaceFunction (IntegralCriticalFlatHeightBits.companionValue F) :=
  ((IntegralCriticalNativeDispatcherBits.evaluator F h a).precompose
    (IntegralCriticalFlatEulerBits.next F.toParameters .companion)
    (IntegralCriticalFlatEulerBits.next_FP F.toParameters h.task.toAccess .companion)).congr
      (funext fun q => IntegralCriticalActualEntryBits.companion_value F q)

end LeanCanny.Algebra.IntegralCriticalNativeSamplerBits
