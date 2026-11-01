/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeEulerLower
public import LeanCanny.Algebra.IntegralMixedVirtualFoldTransport
/-! # Native finite folds over actual virtual arithmetic children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem frame_coordinate (P : Parameters) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (IntegralCriticalFlatCoordinateQuery.writer P p z) := by
  refine ⟨IntegralCriticalFlatCoordinateQuery.writer_root P p z, IntegralCriticalFlatCoordinateQuery.writer_length P p z, ?_⟩
  apply IntegralMixedRoutineTaskBits.lower_phase P (pairFst z) _ (IntegralCriticalFlatCoordinateQuery.writer_birth P p z)
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatCoordinateQuery.writer_other P p z .slot14 (by decide)]
  · rw [IntegralCriticalFlatCoordinateQuery.writer_phase]
    exact hp

abbrev FrozenSumRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i < (source P F).arity q,
    reply (IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm (pair q (BinaryNatCode.encode i))) =
      IntegralMixedVirtualSnapshotBits.frozenTerm P F
        (IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm (pair q (BinaryNatCode.encode i)))

theorem frozenSum_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : FrozenSumRepliesAt P F reply q) :
    IntegralCriticalFlatFrozenSumBits.RepliesAt P (source P F).toGradient.toFrozen reply q := by
  intro i hi
  exact (he i hi).trans (IntegralMixedVirtualFoldBits.frozenSum_child P F q i
    (hi.le.trans (IntegralMixedVirtualFoldBits.arity_cap P F g q)))

noncomputable def frozenSumMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralCriticalFlatFrozenSumBits.program P (source P F).toGradient.toFrozen).controller
  certificates := IntegralCriticalFlatFrozenSumBits.certificates P a _ (sourceAccess P a F h).toGradient.toFrozen
  selected := selectedValid P .frozenPowerSum
  selected_FP := selectedValid_FP P a .frozenPowerSum
  model := IntegralMixedVirtualSnapshotBits.frozenSum P F
  clock := (source P F).arity
  clock_binary := BinaryFn.ofUnary (sourceAccess P a F h).arity
  stateBound := IntegralCriticalFlatFrozenSumBits.stateBound (source P F).toGradient.toFrozen
  stateBound_unary := IntegralCriticalFlatFrozenSumBits.stateBound_unary _ (sourceAccess P a F h).toGradient.toFrozen

theorem frozenSum_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .frozenPowerSum q = true → FrozenSumRepliesAt P F reply q) :
    Correct (frozenSumMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatFrozenSumBits.halted_after P _ reply q
  · intro q t hq hh
    exact (IntegralCriticalFlatFrozenSumBits.output_when_halted_local P _ reply q
      (frozenSum_replies P F g reply q (he q hq)) t hh).trans
        (IntegralMixedVirtualSnapshotBits.frozenSum_eq P F q).symm
  · intro q t hq
    exact IntegralCriticalFlatFrozenSumBits.state_length_local P _ reply q
      (frozenSum_replies P F g reply q (he q hq)) t
  · intro q c budget hq hc
    have HP := ((selectedValid_iff P .frozenPowerSum q).mp hq).2.2
    change phase q = 10 at HP
    have HC := fold_requests_bound (IntegralCriticalFlatFrozenSumBits.program P (source P F).toGradient.toFrozen) reply budget q c hc
    obtain ⟨i, _, rfl⟩ := (IntegralCriticalFlatFrozenSumBits.requests_iff P _ reply q c).mp HC
    simpa only [pairFst_pair] using frame_coordinate P .frozenPowerTerm (pair q (BinaryNatCode.encode i))
      (by simp only [pairFst_pair]; change 9 < phase q; omega)

abbrev SumRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i < (source P F).free q,
    reply (IntegralCriticalFlatEulerRowsBits.sumTask P (source P F) (pair q (BinaryNatCode.encode i))) =
      IntegralMixedVirtualFoldBits.product P F
        (IntegralCriticalFlatEulerRowsBits.sumTask P (source P F) (pair q (BinaryNatCode.encode i)))

theorem sum_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : SumRepliesAt P F reply q) :
    ∀ i < (source P F).free q,
      reply (IntegralCriticalFlatEulerRowsBits.sumTask P (source P F) (pair q (BinaryNatCode.encode i))) =
        residueBits ((source P F).summand q i : ZMod ((source P F).modulus q)) := by
  intro i hi
  exact (he i hi).trans ((IntegralMixedVirtualFoldBits.sum_child P F g q i hi).trans
    (IntegralEulerBits.term_packet (source P F) q ⟨i, hi⟩))

noncomputable def sumMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralCriticalFlatGenericEulerBits.sumProgram P (source P F)).controller
  certificates := IntegralCriticalFlatGenericEulerBits.sum_certificates P a _ (sourceAccess P a F h)
  selected := selectedValid P .eulerSum
  selected_FP := selectedValid_FP P a .eulerSum
  model := IntegralMixedVirtualSnapshotBits.sum P F
  clock := (source P F).free
  clock_binary := BinaryFn.ofUnary (sourceAccess P a F h).free
  stateBound := IntegralCriticalFlatGenericEulerBits.scanStateBound (source P F) (source P F).free
  stateBound_unary := IntegralCriticalFlatGenericEulerBits.sum_stateBound_unary _ (sourceAccess P a F h)

theorem sum_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .eulerSum q = true → SumRepliesAt P F reply q) :
    Correct (sumMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatGenericEulerBits.sum_halted_after P _ reply q
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericEulerBits.sum_output_when_halted_at P _ reply q
      (sum_replies P F g reply q (he q hq)) t hh).trans (IntegralMixedVirtualSnapshotBits.sum_eq P F q).symm
  · intro q t hq
    have H := IntegralCriticalFlatGenericEulerBits.sum_state_length_at P (source P F) reply q
      (sum_replies P F g reply q (he q hq)) t
    rw [show (IntegralCriticalFlatGenericEulerBits.sumProgram P (source P F)).initial q =
      (IntegralCriticalFlatGenericEulerBits.sumProgram P (source P F)).controller.initial q from rfl] at H
    simpa only [sumMachine, IntegralCriticalFlatGenericEulerBits.scanStateBound, Turing.MultiTapeTM.encNat_apply,
      Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H
  · intro q c budget hq hc
    have HP := ((selectedValid_iff P .eulerSum q).mp hq).2.2
    change phase q = 14 at HP
    have HC := fold_requests_bound (IntegralCriticalFlatGenericEulerBits.sumProgram P (source P F)) reply budget q c hc
    obtain ⟨i, _, rfl⟩ := (IntegralCriticalFlatGenericEulerBits.sum_requests_iff P _ reply q c).mp HC
    simpa only [IntegralCriticalFlatEulerRowsBits.sumTask, IntegralEulerBits.termQuery, pairFst_pair] using
      frame_spatial P .coordinateGradientProduct 0 (IntegralEulerBits.termQuery (source P F) (pair q (BinaryNatCode.encode i)))
        (by simp only [IntegralEulerBits.termQuery, pairFst_pair]; change 13 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
