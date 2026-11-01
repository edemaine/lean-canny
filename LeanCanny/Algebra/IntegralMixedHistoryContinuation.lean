/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistoryOrigin

/-! # Mixed continuation of an already retained integer-root bank

Continuation starts from the actual finite initial sampler and bank. It
keeps every existing scalar birth, adds one prefix variable per command,
and charges physical critical variables only for critical commands.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralHistorySampler
open scoped Classical

noncomputable def continueRun {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B m ι) : (cs : List (Command n B)) → m + cs.length ≤ S + 1 →
      State P S B (m + cs.length) (Index ι cs)
  | [], _ => initial
  | c :: cs, hcs => step (continueRun initial cs (by simp only [List.length_cons] at hcs; omega))
      (by simp only [List.length_cons] at hcs; omega) c

noncomputable def retainIntegerBank {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : IntegralIntegerRootBank.State S B m ι)
    (hcap : PurePowerReductionBounds.dimension (n + 1) P.degree ≤ 2 ^ B) : State P S B m ι where
  sampler := x.sampler
  bank := x.bank
  denominator_ne_zero := x.denominator_ne_zero
  critical_cap := hcap


end LeanCanny.Algebra.IntegralMixedHistoryScript
