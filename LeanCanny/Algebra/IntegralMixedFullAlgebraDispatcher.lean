/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCriticalOutside
public import LeanCanny.Algebra.IntegralMixedFullProducerOutside
/-! # One native routine dispatcher for critical arithmetic and actual producers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  critical : IntegralMixedFullCriticalDispatcherBits.Controls P D
  producer : IntegralMixedFullProducerDispatcherBits.Controls P D

noncomputable def node (P : Parameters) (a : Access P) (code : ℕ) (M : Machine) : PhaseNode (IntegralMixedRoutineTaskBits.routine P) where
  machine := M.withGuard (fun q => decide (IntegralMixedRoutineTaskBits.routine P q = code))
    ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const code)).flag_mem_FP
  code := code
  selected_phase _ hs := of_decide_eq_true hs

noncomputable def criticalNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  node P a 1 (IntegralMixedFullCriticalDispatcherBits.machine P a D h.critical)
noncomputable def producerNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  node P a 6 (IntegralMixedFullProducerDispatcherBits.machine P a D h.producer)
noncomputable def nodes (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  [criticalNode P a D h, producerNode P a D h]
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  phaseDispatch (nodes P a D h) zero

theorem distinct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :
    ((nodes P a D h).map PhaseNode.code).Nodup := by change [1, 6].Nodup; decide

theorem model_critical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) :
    (machine P a D h).model q = (IntegralMixedFullCriticalDispatcherBits.machine P a D h.critical).model q :=
  phaseDispatch_model_selected _ _ q (criticalNode P a D h) (distinct P a D h) List.mem_cons_self (decide_eq_true hr)

theorem model_producer (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 6) :
    (machine P a D h).model q = (IntegralMixedFullProducerDispatcherBits.machine P a D h.producer).model q :=
  phaseDispatch_model_selected _ _ q (producerNode P a D h) (distinct P a D h)
    (List.mem_cons_of_mem _ List.mem_cons_self) (decide_eq_true hr)

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (decide (IntegralMixedRoutineTaskBits.routine P q = 1) || (decide (IntegralMixedRoutineTaskBits.routine P q = 6) || true)) = true
  rw [Bool.or_true, Bool.or_true]

end LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
