/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarModel
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
/-! # Seven-routine native dispatcher with charged current-bank slope restoration -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Controls (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  scalar : IntegralMixedFramedCurrentQScalarBits.Controls P D H
  critical : IntegralMixedFramedCriticalBits.Controls P D H
  normalization : IntegralMixedFramedNormalizationBits.Controls P D H
  producer : IntegralMixedFramedProducerBits.Controls P D H

noncomputable def component (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) : Fin 7 → Machine
  | 0 => IntegralMixedFramedCurrentQScalarBits.machine P a D H h.scalar
  | 1 => IntegralMixedFramedCriticalBits.machine P a D H h.critical
  | 2 => IntegralMixedFramedEntryBits.machine P a D H h.critical
  | 3 => IntegralMixedFramedDeterminantBits.machine P a D H h.critical
  | 4 => IntegralMixedFramedNormalizationBits.rawMachine P a D H h.normalization
  | 5 => IntegralMixedFramedNormalizationBits.machine P a D H h.normalization
  | 6 => IntegralMixedFramedProducerBits.machine P a D H h.producer

noncomputable def guard (P : Parameters) (r : Fin 7) (q : List Bool) : Bool :=
  decide (IntegralMixedRoutineTaskBits.routine P q = r.val)
theorem guard_FP (P : Parameters) (a : Access P) (r : Fin 7) : (fun q => [guard P r q]) ∈ FP :=
  ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const r.val)).flag_mem_FP

noncomputable def node (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) : PhaseNode (IntegralMixedRoutineTaskBits.routine P) where
  machine := (component P a D H h r).withGuard (guard P r) (guard_FP P a r)
  code := r.val
  selected_phase _ hs := of_decide_eq_true hs

noncomputable def nodes (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  [node P a D H h 0, node P a D H h 1, node P a D H h 2, node P a D H h 3, node P a D H h 4, node P a D H h 5, node P a D H h 6]
noncomputable def machine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) := phaseDispatch (nodes P a D H h) zero

attribute [local irreducible] component

private theorem guard_model (M : Machine) (s : List Bool → Bool)
    (hs : (fun q => [s q]) ∈ FP) (q : List Bool) : (M.withGuard s hs).model q = M.model q := rfl
private theorem guard_selected (M : Machine) (s : List Bool → Bool)
    (hs : (fun q => [s q]) ∈ FP) (q : List Bool) : (M.withGuard s hs).selected q = s q := rfl

theorem nodes_distinct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) : ((nodes P a D H h).map PhaseNode.code).Nodup := by
  change ([0,1,2,3,4,5,6] : List ℕ).Nodup
  decide

theorem node_mem (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) : node P a D H h r ∈ nodes P a D H h := by
  fin_cases r
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem model_component (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = r.val) :
    (machine P a D H h).model q = (component P a D H h r).model q := by
  have HS : (node P a D H h r).machine.selected q = true := by
    simp only [node, guard_selected, guard, decide_eq_true_eq, hr]
  exact (phaseDispatch_model_selected (nodes P a D H h) zero q (node P a D H h r)
    (nodes_distinct P a D H h) (node_mem P a D H h r) HS).trans (guard_model _ _ _ q)

private theorem dispatch_selected {code : List Bool → ℕ} (ns : List (PhaseNode code)) (q : List Bool) :
    (phaseDispatch ns zero).selected q = true := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    change (n.machine.selected q || (phaseDispatch ns zero).selected q) = true
    rw [ih, Bool.or_true]

theorem selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) : (machine P a D H h).selected q = true :=
  dispatch_selected _ q

end LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
