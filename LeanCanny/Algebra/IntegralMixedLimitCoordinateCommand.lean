/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateCorrelated

/-! # The actual tagged command for a selected limit-coordinate birth

The advertised truncation degree is bounded by the original spatial cap. The
tagged interpreter and the correlated normalized scalar realization are the
same state, with no new evaluator or algebraic-degree feedback.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinate
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem degree_auxiliaryCap (P : SpatialSource n) (r : Rule n) :
    degree P r≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree := by
  have H := IntegralMixedExceptionalBounds.coordinateCap_le P.degree r
  change PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree≤_
  unfold IntegralMixedExceptionalBounds.auxiliaryCap
  omega

noncomputable def command (x : State P S B m ι) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) (d : ℕ) (hd : d≤degree P r) :
    IntegralMixedFullHistoryScript.Command P B :=
  .cut r (.limitCoordinate j c) d (hd.trans (degree_auxiliaryCap P r)) (hd.trans (degree_cap x r))

noncomputable def instruction (x : State P S B m ι) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) (d : ℕ) (hd : d≤degree P r) :
    IntegralMixedFramedHistoryScript.Instruction n B := ⟨P,x.critical_cap,command x r j c d hd⟩

variable [Fintype ι]

theorem command_step (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) (d : ℕ) (hd : d≤degree P r) :
    IntegralMixedFullHistoryScript.step x hm (command x r j c d hd)=step x hm r j c d := rfl

end LeanCanny.Algebra.IntegralMixedLimitCoordinate
