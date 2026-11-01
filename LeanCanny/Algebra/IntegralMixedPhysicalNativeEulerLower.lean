/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeFrozenLower
/-! # Native Euler lower rows over the actual physical source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
open IntegralMixedPhysicalNativeLowerBits
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev lowerProgram (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericEulerBits.lowerProgram P (source P F)
noncomputable abbrev gradientQuery (P : Parameters) (F : Family) :=
  IntegralEulerBits.lowerGradientQuery (source P F) (IntegralCriticalFlatEulerRowsBits.selected P (source P F))

noncomputable def lowerMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := (lowerProgram P F).controller
  certificates := (lowerProgram P F).certificates (IntegralCriticalFlatGenericEulerBits.lower_controls P a (source P F) (sourceAccess P a F h))
  selected := selected P .eulerLower
  selected_FP := selected_FP P a .eulerLower
  model := IntegralMixedPhysicalSnapshotBits.lower P F
  clock := fun _ => 1
  clock_binary := BinaryFn.const 1
  stateBound := IntegralCriticalFlatGenericEulerBits.lowerStateBound (source P F)
  stateBound_unary := IntegralCriticalFlatGenericEulerBits.lowerStateBound_unary _ (sourceAccess P a F h)

abbrev LowerRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ((IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val = IntegralEulerBits.objectiveRank (source P F) q →
    reply (IntegralCriticalFlatEulerBits.next P .eulerObjective q) =
      IntegralMixedPhysicalSnapshotBits.objective P F (IntegralCriticalFlatEulerBits.next P .eulerObjective q)) ∧
  ((IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val ≠ IntegralEulerBits.objectiveRank (source P F) q →
    reply (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (gradientQuery P F q)) =
      IntegralMixedPhysicalSpatialBits.cleared P F (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (gradientQuery P F q)))

theorem lower_gradient_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPhysicalSpatialBits.cleared P F (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (gradientQuery P F q)) =
      (IntegralCriticalGradientBits.family (source P F).toGradient).value (gradientQuery P F q) :=
  IntegralMixedPhysicalSpatialBits.spatial_derivative_child P F .clearedGridSum q
    (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q) _
    (IntegralCriticalFlatEulerRowsBits.selected_le P (source P F) q) (get_le P .target q)

theorem lower_objective_reply (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : LowerRepliesAt P F reply q)
    (ho : (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val = IntegralEulerBits.objectiveRank (source P F) q) :
    reply (IntegralCriticalFlatEulerBits.next P .eulerObjective q) = (source P F).objectiveValue q :=
  (he.1 ho).trans ((IntegralMixedPhysicalSnapshotBits.objective_next P F _ q).trans (IntegralMixedPhysicalSnapshotBits.objective_eq P F q))

theorem lower_gradient_reply (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : LowerRepliesAt P F reply q)
    (hg : (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val ≠ IntegralEulerBits.objectiveRank (source P F) q) :
    reply (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (gradientQuery P F q)) =
      (IntegralCriticalGradientBits.family (source P F).toGradient).value (gradientQuery P F q) :=
  (he.2 hg).trans (lower_gradient_child P F q)

theorem lower_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool)
    (he : ∀ q, selected P .eulerLower q = true → LowerRepliesAt P F reply q) :
    Correct (lowerMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (lowerProgram P F).halted_after reply q
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericEulerBits.lower_output_when_halted_at P _ reply q
      (lower_objective_reply P F reply q (he q hq)) (lower_gradient_reply P F reply q (he q hq)) t hh).trans
        (IntegralMixedPhysicalSnapshotBits.lower_eq P F q).symm
  · intro q t hq
    exact IntegralCriticalFlatGenericEulerBits.lower_state_length_at P _ reply q
      (lower_objective_reply P F reply q (he q hq)) (lower_gradient_reply P F reply q (he q hq)) t
  · intro q c budget hq hc
    have HP := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .eulerLower q).mp (selected_raw P .eulerLower q hq)).2.2
    change phase q = 16 at HP
    have HC := ((lowerProgram P F).requests_iff reply budget q c).mp hc
    apply Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) HC.2)
    change IntegralMixedRoutineTaskBits.Frame P q
      (if (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val = IntegralEulerBits.objectiveRank (source P F) q
        then IntegralCriticalFlatEulerBits.next P .eulerObjective q
        else IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (gradientQuery P F q))
    split_ifs
    · exact frame_next P .eulerObjective q (by change 15 < phase q; omega)
    · have HF := frame_spatial P .clearedGridSum 1 (gradientQuery P F q)
      have HG : pairFst (gradientQuery P F q) = q := pairFst_pair _ _
      rw [HG] at HF
      apply HF
      change 8 < phase q
      omega
end LeanCanny.Algebra.IntegralMixedPhysicalContextBits
