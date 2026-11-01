/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeObjective
/-! # Native frozen constant with a charged scalar-leading child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
open scoped Classical
open IntegralMixedPhysicalNativeLowerBits
set_option backward.isDefEq.respectTransparency false

noncomputable def originalLeadingValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((source P F).leading q : ZMod (modulus P q))

noncomputable def frozenConstantProgram (P : Parameters) (F : Family) :=
  IntegralMixedVirtualFrozenRequestBits.program (source P F).toGradient.toFrozen
    (IntegralMixedScalarQueryBits.originalLeading P) (IntegralCriticalFlatEulerBits.next P .frozenPowerSum)

noncomputable def frozenConstantMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (frozenConstantProgram P F).controller
  certificates := IntegralMixedVirtualFrozenRequestBits.certificates _ (sourceAccess P a F h).toGradient.toFrozen _ _
    (IntegralMixedScalarQueryBits.scalarQuery_FP P a .originalCoefficient)
    (IntegralCriticalFlatEulerBits.next_FP P a .frozenPowerSum)
  selected := selected P .frozenConstant
  selected_FP := selected_FP P a .frozenConstant
  model := IntegralMixedPhysicalSnapshotBits.frozenConstant P F
  clock := (frozenConstantProgram P F).count
  clock_binary := BinaryFn.ite (IntegralFrozenPowerBits.zeroTarget_fppred _ (sourceAccess P a F h).toGradient.toFrozen)
    (BinaryFn.const 2) (BinaryFn.const 0)
  stateBound := IntegralMixedVirtualFrozenRequestBits.stateBound (source P F).toGradient.toFrozen
  stateBound_unary := IntegralMixedVirtualFrozenRequestBits.stateBound_unary _ (sourceAccess P a F h).toGradient.toFrozen

abbrev FrozenConstantRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  IntegralFrozenPowerBits.zeroTarget (source P F).toGradient.toFrozen q →
    reply (IntegralMixedScalarQueryBits.originalLeading P q) = originalLeadingValue P F q ∧
    reply (IntegralCriticalFlatEulerBits.next P .frozenPowerSum q) =
      IntegralMixedPhysicalSnapshotBits.frozenSum P F (IntegralCriticalFlatEulerBits.next P .frozenPowerSum q)

theorem frozenConstant_replies (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (q : List Bool) (he : FrozenConstantRepliesAt P F reply q)
    (hz : IntegralFrozenPowerBits.zeroTarget (source P F).toGradient.toFrozen q) :
    reply (IntegralMixedScalarQueryBits.originalLeading P q) = (sourceAccess P a F h).leading q ∧
    reply (IntegralCriticalFlatEulerBits.next P .frozenPowerSum q) = (source P F).toGradient.toFrozen.sumValue q :=
  ⟨(he hz).1.trans ((sourceAccess P a F h).leading_eq q).symm,
    (he hz).2.trans ((IntegralMixedPhysicalSnapshotBits.frozenSum_next P F _ q).trans
      (IntegralMixedPhysicalSnapshotBits.frozenSum_eq P F q))⟩

theorem frozenConstant_value_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (q : List Bool) (he : FrozenConstantRepliesAt P F reply q) :
    (frozenConstantProgram P F).value reply q = IntegralMixedPhysicalSnapshotBits.frozenConstant P F q :=
  (IntegralMixedVirtualFrozenRequestBits.value_at _ (sourceAccess P a F h).toGradient.toFrozen _ _ reply q
    (fun hz => (frozenConstant_replies P a F h reply q he hz).1)
    (fun hz => (frozenConstant_replies P a F h reply q he hz).2)).trans
      (IntegralMixedPhysicalSnapshotBits.frozenConstant_eq P F q).symm

theorem frozenConstant_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool)
    (he : ∀ q, selected P .frozenConstant q = true → FrozenConstantRepliesAt P F reply q) :
    Correct (frozenConstantMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (frozenConstantProgram P F).halted_after reply q
  · intro q t hq hh
    exact ((frozenConstantProgram P F).output_when_halted reply q t hh).trans
      (frozenConstant_value_at P a F h reply q (he q hq))
  · intro q t hq
    exact IntegralMixedVirtualFrozenRequestBits.state_length_at _ (sourceAccess P a F h).toGradient.toFrozen _ _ reply q
      (fun hz => (frozenConstant_replies P a F h reply q (he q hq) hz).1)
      (fun hz => (frozenConstant_replies P a F h reply q (he q hq) hz).2) t
  · intro q c budget hq hc
    have HP := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .frozenConstant q).mp (selected_raw P .frozenConstant q hq)).2.2
    have HR := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .frozenConstant q).mp (selected_raw P .frozenConstant q hq)).2.1
    change phase q = 11 at HP
    have HC := fold_requests_bound (frozenConstantProgram P F) reply budget q c hc
    rcases (IntegralMixedVirtualFrozenRequestBits.requests_iff _ _ _ reply q c).mp HC with ⟨_, rfl | rfl⟩
    · exact IntegralMixedScalarQueryBits.scalar_frame P .originalCoefficient q (by rw [HR]; decide)
    · exact frame_next P .frozenPowerSum q (by change 10 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedPhysicalContextBits
