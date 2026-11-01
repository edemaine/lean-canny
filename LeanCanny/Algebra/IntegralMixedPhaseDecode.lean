/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineTask
/-! # Every bounded task phase has its literal algorithm tag -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhaseDecode
open IntegralCriticalHistoryTask

def decode : ℕ → Phase
  | 0 => .originalCoefficient | 1 => .derivativeCoefficient | 2 => .clearedHeight
  | 3 => .monomialFactor | 4 => .factorPower | 5 => .productEntry | 6 => .productPower
  | 7 => .originalGridTerm | 8 => .clearedGridSum | 9 => .frozenPowerTerm | 10 => .frozenPowerSum
  | 11 => .frozenConstant | 12 => .frozenLower | 13 => .coordinateGradientProduct | 14 => .eulerSum
  | 15 => .eulerObjective | 16 => .eulerLower | 17 => .reductionEntry | 18 => .reductionPower
  | 19 => .actionEntry | 20 => .actionPower | 21 => .momentEntry | 22 => .momentPower
  | 23 => .relativeFactor | 24 => .relativePower | 25 => .criticalCoefficient | _ => .companion

theorem code (k : ℕ) (hk : k < 27) : (decode k).code = k := by
  interval_cases k <;> rfl

theorem task (q : List Bool) : isPhase (decode (phase q)) q :=
  (code (phase q) (IntegralMixedRoutineTaskBits.phase_lt q)).symm

end LeanCanny.Algebra.IntegralMixedPhaseDecode
