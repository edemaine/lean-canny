/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextProducts
public import LeanCanny.Algebra.IntegralMixedVirtualNativeValidBranch
public import LeanCanny.Algebra.IntegralMixedVirtualSnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatFrozenLower
/-! # Native Euler objective over the actual virtual algebra -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
open IntegralMixedVirtualNativeLowerBits
set_option backward.isDefEq.respectTransparency false

theorem frame_next (P : Parameters) (p : Phase) (q : List Bool) (hp : p.code < phase q) :
    IntegralMixedRoutineTaskBits.Frame P q (IntegralCriticalFlatEulerBits.next P p q) := by
  refine ⟨IntegralCriticalFlatEulerBits.next_root P p q, ?_, ?_⟩
  · exact child_length P id (birth P) p (RankedHistoryFields.read (numericCap P) 16) q (min_le_right _ _)
  apply IntegralMixedRoutineTaskBits.lower_phase P q _ (IntegralCriticalFlatEulerBits.next_birth P p q)
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatEulerBits.next_get]
  · rw [IntegralCriticalFlatEulerBits.next_phase]
    exact hp

theorem fold_requests_bound (P : RecursiveFold.Program) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hc : P.controller.Requests reply budget q c) : P.controller.Requests reply P.count q c := by
  obtain ⟨t, _, hh, _, he⟩ := hc
  have HI : min t (P.count q) < P.count q := by
    rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at hh
    have H : ¬ P.count q ≤ min t (P.count q) := of_decide_eq_false hh
    omega
  apply (P.requests_iff reply q c).mpr
  refine ⟨min t (P.count q), HI, ?_⟩
  rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at he
  exact he

noncomputable def objectiveProgram (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericEulerBits.objectiveProgram P (source P F)

noncomputable def objectiveMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (objectiveProgram P F).controller
  certificates := IntegralCriticalFlatGenericEulerBits.objective_certificates P a (source P F) (sourceAccess P a F h)
  selected := selected P .eulerObjective
  selected_FP := selected_FP P a .eulerObjective
  model := IntegralMixedVirtualSnapshotBits.objective P F
  clock := fun _ => 2
  clock_binary := BinaryFn.const 2
  stateBound := IntegralCriticalFlatFrozenLowerBits.stateBound (source P F).toGradient.toFrozen
  stateBound_unary := IntegralCriticalFlatFrozenLowerBits.stateBound_unary _ (sourceAccess P a F h).toGradient.toFrozen

abbrev ObjectiveRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  reply (IntegralCriticalFlatEulerBits.next P .frozenLower q) =
    IntegralMixedVirtualSnapshotBits.frozenLower P F (IntegralCriticalFlatEulerBits.next P .frozenLower q) ∧
  reply (IntegralCriticalFlatEulerBits.next P .eulerSum q) =
    IntegralMixedVirtualSnapshotBits.sum P F (IntegralCriticalFlatEulerBits.next P .eulerSum q)

theorem objective_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : ObjectiveRepliesAt P F reply q) :
    reply (IntegralCriticalFlatEulerBits.next P .frozenLower q) = (source P F).toGradient.toFrozen.lowerValue q ∧
    reply (IntegralCriticalFlatEulerBits.next P .eulerSum q) = (source P F).sumValue q := by
  exact ⟨he.1.trans ((IntegralMixedVirtualSnapshotBits.frozenLower_next P F _ q).trans
    (IntegralMixedVirtualSnapshotBits.frozenLower_eq P F q)),
    he.2.trans ((IntegralMixedVirtualSnapshotBits.sum_next P F _ q).trans
      (IntegralMixedVirtualSnapshotBits.sum_eq P F q))⟩

theorem objective_post (S : IntegralEulerBits.Source) (q : List Bool) :
    IntegralEulerBits.ObjectiveStage.post S (pair q (pair (S.toGradient.toFrozen.lowerValue q) (S.sumValue q))) = S.objectiveValue q := by
  unfold IntegralEulerBits.ObjectiveStage.post
  simp only [pairFst_pair, pairSnd_pair]
  exact IntegralEulerBits.objective_value S q

theorem objective_value_at (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : ObjectiveRepliesAt P F reply q) :
    (objectiveProgram P F).value reply q = IntegralMixedVirtualSnapshotBits.objective P F q := by
  have HR := objective_replies P F reply q he
  change (TwoCall.program _ _ (IntegralEulerBits.ObjectiveStage.post (source P F))).value reply q = _
  rw [TwoCall.value_eq, HR.1, HR.2, objective_post]
  exact (IntegralMixedVirtualSnapshotBits.objective_eq P F q).symm

theorem objective_state_at (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : ObjectiveRepliesAt P F reply q) (t : ℕ) :
    (RecursiveFold.encState (((objectiveProgram P F).controller.reference reply)^[t]
      ((objectiveProgram P F).initial q))).length ≤ IntegralCriticalFlatFrozenLowerBits.stateBound (source P F).toGradient.toFrozen q := by
  let : NeZero ((source P F).modulus q) := ⟨(source P F).modulus_ne_zero q⟩
  have HB (z : ZMod ((source P F).modulus q)) : (residueBits z).length ≤ ((source P F).modulus q).size := residueBits_length_le _ _
  have HL : ((source P F).toGradient.toFrozen.lowerValue q).length ≤ ((source P F).modulus q).size := by
    unfold IntegralFrozenPowerBits.Source.lowerValue
    exact HB _
  have HO : ((source P F).objectiveValue q).length ≤ ((source P F).modulus q).size := by
    unfold IntegralEulerBits.Source.objectiveValue
    exact HB _
  have H := TwoCall.state_length (IntegralCriticalFlatEulerBits.next P .frozenLower)
    (IntegralCriticalFlatEulerBits.next P .eulerSum) (IntegralEulerBits.ObjectiveStage.post (source P F)) reply q t
  have HR := objective_replies P F reply q he
  rw [HR.1, HR.2, objective_post] at H
  change _ ≤ 2 * q.length + 2 * (2 : ℕ).size + ((source P F).modulus q).size + 2
  have HE : (encNat 2).length = (2 : ℕ).size := by simp [encNat_apply, Nat.size_eq_bits_len]
  rw [HE] at H
  exact H.trans (by omega)

theorem objective_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (he : ∀ q, selected P .eulerObjective q = true → ObjectiveRepliesAt P F reply q) :
    Correct (objectiveMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (objectiveProgram P F).halted_after reply q
  · intro q t hq hh
    exact ((objectiveProgram P F).output_when_halted reply q t hh).trans (objective_value_at P F reply q (he q hq))
  · intro q t hq
    exact objective_state_at P F reply q (he q hq) t
  · intro q c budget hq hc
    have HP := (selected_base P .eulerObjective q hq).2.2
    change phase q = 15 at HP
    have HC := fold_requests_bound (objectiveProgram P F) reply budget q c hc
    rcases (IntegralEulerBits.ObjectiveStage.requests_iff (source P F) _ _ reply q c).mp HC with rfl | rfl
    · exact frame_next P .frozenLower q (by change 12 < phase q; omega)
    · exact frame_next P .eulerSum q (by change 14 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedVirtualContextBits
