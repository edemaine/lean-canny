/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFrozenConstant
public import LeanCanny.Algebra.IntegralMixedVirtualSpatialModel
/-! # Native virtual frozen lower rows with actual cleared and constant children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem frame_spatial (P : Parameters) (p : Phase) (x : ℕ) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (IntegralCriticalFlatEulerRowsBits.spatial P p x z) := by
  refine ⟨IntegralCriticalFlatEulerRowsBits.spatial_root P p x z, ?_, ?_⟩
  · exact child_length P pairFst (birth P ∘ pairFst) p (IntegralCriticalFlatEulerRowsBits.spatialReader P x) z (min_le_right _ _)
  apply IntegralMixedRoutineTaskBits.lower_phase P (pairFst z) _ (IntegralCriticalFlatEulerRowsBits.spatial_birth P p x z)
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatEulerRowsBits.spatial_other P p x z .slot14 (by decide) (by decide) (by decide)]
  · rw [IntegralCriticalFlatEulerRowsBits.spatial_phase]
    exact hp

noncomputable def frozenLowerProgram (P : Parameters) (F : Family) :=
  IntegralCriticalFlatFrozenLowerBits.program P (source P F).toGradient.toFrozen

noncomputable def frozenLowerMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (frozenLowerProgram P F).controller
  certificates := IntegralCriticalFlatFrozenLowerBits.certificates P a _ (sourceAccess P a F h).toGradient.toFrozen
  selected := selectedValid P .frozenLower
  selected_FP := selectedValid_FP P a .frozenLower
  model := IntegralMixedVirtualSnapshotBits.frozenLower P F
  clock := fun _ => 2
  clock_binary := BinaryFn.const 2
  stateBound := IntegralCriticalFlatFrozenLowerBits.stateBound (source P F).toGradient.toFrozen
  stateBound_unary := IntegralCriticalFlatFrozenLowerBits.stateBound_unary _ (sourceAccess P a F h).toGradient.toFrozen

abbrev FrozenLowerRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  reply (IntegralCriticalFlatFrozenLowerBits.clearedTask P (source P F).toGradient.toFrozen q) =
    IntegralMixedVirtualSpatialBits.cleared P F (IntegralCriticalFlatFrozenLowerBits.clearedTask P (source P F).toGradient.toFrozen q) ∧
  reply (IntegralCriticalFlatEulerBits.next P .frozenConstant q) =
    IntegralMixedVirtualSnapshotBits.frozenConstant P F (IntegralCriticalFlatEulerBits.next P .frozenConstant q)

theorem frozenLower_cleared_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualSpatialBits.cleared P F (IntegralCriticalFlatFrozenLowerBits.clearedTask P (source P F).toGradient.toFrozen q) =
      (source P F).toGradient.toFrozen.toSource.value q := by
  rw [IntegralMixedVirtualSpatialBits.original_snapshot]
  exact IntegralMixedVirtualSpatialBits.spatial_original_child P F .clearedGridSum q
    (get P .derivative q) (get P .target q) (get_le P .derivative q) (get_le P .target q)

theorem frozenLower_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : FrozenLowerRepliesAt P F reply q) :
    reply (IntegralCriticalFlatFrozenLowerBits.clearedTask P (source P F).toGradient.toFrozen q) =
      (source P F).toGradient.toFrozen.toSource.value q ∧
    reply (IntegralCriticalFlatEulerBits.next P .frozenConstant q) = (source P F).toGradient.toFrozen.constantValue q :=
  ⟨he.1.trans (frozenLower_cleared_child P F q), he.2.trans
    ((IntegralMixedVirtualSnapshotBits.frozenConstant_next P F _ q).trans (IntegralMixedVirtualSnapshotBits.frozenConstant_eq P F q))⟩

theorem frozenLower_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .frozenLower q = true → FrozenLowerRepliesAt P F reply q) :
    Correct (frozenLowerMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (frozenLowerProgram P F).halted_after reply q
  · intro q t hq hh
    have HR := frozenLower_replies P F reply q (he q hq)
    exact (IntegralCriticalFlatFrozenLowerBits.output_when_halted_local P _ reply q HR.1 HR.2 t hh).trans
      (IntegralMixedVirtualSnapshotBits.frozenLower_eq P F q).symm
  · intro q t hq
    have HR := frozenLower_replies P F reply q (he q hq)
    exact IntegralCriticalFlatFrozenLowerBits.state_length_local P (source P F).toGradient.toFrozen reply q HR.1 HR.2 t
  · intro q c budget hq hc
    have HP := ((selectedValid_iff P .frozenLower q).mp hq).2.2
    change phase q = 12 at HP
    have HC := fold_requests_bound (frozenLowerProgram P F) reply budget q c hc
    rcases (IntegralCriticalFlatFrozenLowerBits.requests_iff P _ reply q c).mp HC with rfl | rfl
    · have HF := frame_spatial P .clearedGridSum 0
        (pair q (pair (BinaryNatCode.encode (get P .derivative q)) (BinaryNatCode.encode ((source P F).target q))))
      have HH : 8 < phase q := by omega
      simpa only [IntegralCriticalFlatFrozenLowerBits.clearedTask, pairFst_pair] using
        HF (by simpa only [pairFst_pair, Phase.code] using HH)
    · exact frame_next P .frozenConstant q (by change 11 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
