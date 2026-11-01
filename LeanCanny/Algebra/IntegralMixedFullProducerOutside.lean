/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullProducerCanonical
/-! # The full producer dispatcher rejects requests outside its routine and contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullProducerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] integerMachine physicalMachine cutMachine

theorem model_none (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) (h0 : ¬InContext P 0 0 q) (h1 : ¬InContext P 1 1 q) (h2 : ¬InContext P 2 4 q) :
    (machine P a D h).model q = [] := by
  change (if decide (InContext P 0 0 q) then _ else if decide (InContext P 1 1 q) then _ else if decide (InContext P 2 4 q) then _ else []) = []
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h0),
    ite_eq_right (by simpa only [decide_eq_true_eq] using h1), ite_eq_right (by simpa only [decide_eq_true_eq] using h2)]

theorem model_invalid (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) (hv : ¬IntegralMixedVirtualCaps.valid P q) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun hc => hv hc.1) (fun hc => hv hc.1) (fun hc => hv hc.1)

theorem model_other_routine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 6) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun hc => hr hc.2.1) (fun hc => hr hc.2.1) (fun hc => hr hc.2.1)

theorem model_other_context (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) (hx : 4 < get P .slot15 q) : (machine P a D h).model q = [] := by
  apply model_none
  all_goals intro hc; have := hc.2.2.2; omega

end LeanCanny.Algebra.IntegralMixedFullProducerDispatcherBits
