/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateCommand

/-! # Literal source-framed execution of the constructed limit cut -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem run_limit (initial : State P S B 0 ι) (cs : List (Instruction n B)) (h : cs.length≤S)
    (r : Rule n) (j : Fin (n-r.critical.offset.val+1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source P cs) r))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source P cs) r) :
    let old := run initial cs (h.trans (Nat.le_succ S))
    run initial (IntegralMixedLimitCoordinate.instruction old r j c d hd::cs)
      (by simp only [List.length_cons]; omega)=
    IntegralMixedLimitCoordinate.step old h r j c d := rfl

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
