/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextProducts
public import LeanCanny.Algebra.IntegralMixedVirtualFrozenTransport
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Native virtual frozen-height powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
open IntegralMixedVirtualNativeLowerBits
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev frozenSource (P : Parameters) (F : Family) := (source P F).toGradient.toFrozen
noncomputable abbrev frozenAccess (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) := (sourceAccess P a F h).toGradient.toFrozen
abbrev FrozenPowerRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ¬IntegralCriticalFlatFrozenTermBits.free P (frozenSource P F) q →
    ∀ r t : Fin ((frozenSource P F).rank q),
      reply (IntegralCriticalFlatMatrixQuery.writer P .clearedHeight
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      height P F (IntegralCriticalFlatMatrixQuery.writer P .clearedHeight
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))

theorem frozenPower_replies (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (he : FrozenPowerRepliesAt P F reply q) :
    IntegralCriticalFlatFrozenTermBits.RepliesAt P (frozenSource P F) reply q := by
  intro hn r t
  exact (he hn r t).trans (power_height_child P a F h g q hv r t)

noncomputable def frozenPowerMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveController.Controller.ChoiceState SingleCall.State (List Bool)
  defaultValue := (false, default, [])
  encoding := RecursiveController.Controller.encChoice SingleCall.encState Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatFrozenTermBits.controller P (frozenSource P F) (frozenAccess P a F h)
  certificates := IntegralCriticalFlatFrozenTermBits.certificates P a (frozenSource P F) (frozenAccess P a F h)
  selected := selected P .frozenPowerTerm
  selected_FP := selected_FP P a .frozenPowerTerm
  model := IntegralMixedVirtualSnapshotBits.frozenTerm P F
  clock := IntegralCriticalFlatFrozenTermBits.clock P (frozenSource P F)
  clock_binary := IntegralCriticalFlatFrozenTermBits.clock_binary P a (frozenSource P F) (frozenAccess P a F h)
  stateBound := IntegralCriticalFlatFrozenTermBits.stateBound P (frozenSource P F)
  stateBound_unary := IntegralCriticalFlatFrozenTermBits.stateBound_unary P (frozenSource P F) (frozenAccess P a F h)

theorem frozenPower_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .frozenPowerTerm q = true → FrozenPowerRepliesAt P F reply q) :
    Correct (frozenPowerMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatFrozenTermBits.halted_after_local P (frozenSource P F) (frozenAccess P a F h) reply q
      (frozenPower_replies P a F h g reply q (selected_base P .frozenPowerTerm q hq).1 (he q hq))
  · intro q t hq hh
    exact (IntegralCriticalFlatFrozenTermBits.value_local P (frozenSource P F) (frozenAccess P a F h) reply q
      (frozenPower_replies P a F h g reply q (selected_base P .frozenPowerTerm q hq).1 (he q hq)) t hh).trans
        (IntegralMixedVirtualFoldBits.frozenTerm_packet_eq P F q (get P .slot8 q)).symm
  · intro q t hq
    exact IntegralCriticalFlatFrozenTermBits.state_length_local P (frozenSource P F) (frozenAccess P a F h) reply q
      (frozenPower_replies P a F h g reply q (selected_base P .frozenPowerTerm q hq).1 (he q hq)) t
  · intro q c budget hq hc
    have HP := (selected_base P .frozenPowerTerm q hq).2.2
    change phase q = 9 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatFrozenTermBits.requests_in_bounds_local P (frozenSource P F) (frozenAccess P a F h)
      reply q (frozenPower_replies P a F h g reply q (selected_base P .frozenPowerTerm q hq).1 (he q hq)) budget c hc
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .clearedHeight
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) (by
        simp only [pairFst_pair]
        change 2 < phase q
        omega)

end LeanCanny.Algebra.IntegralMixedVirtualContextBits
