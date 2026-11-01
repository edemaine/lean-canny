/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextLowerReplies
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Native virtual arithmetic dispatcher for phases zero to sixteen -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualContextBits NativeControllerBranch
open IntegralMixedVirtualNativeLowerBits (originalScalar)
set_option backward.isDefEq.respectTransparency false

noncomputable def node (P : Parameters) (p : Phase) (M : Machine)
    (hs : M.selected = selected P p) : PhaseNode phase where
  machine := M
  code := p.code
  selected_phase q hq := ((IntegralMixedVirtualNativeLowerBits.selectedValid_iff P p q).mp
    (selected_raw P p q (hs ▸ hq))).2.2

noncomputable def nodes (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : List (PhaseNode phase) :=
  [node P .originalCoefficient (originalMachine P a F h ha) rfl,
   node P .derivativeCoefficient (derivativeMachine P a F h) rfl,
   node P .clearedHeight (heightMachine P a F) rfl,
   node P .monomialFactor (monomialMachine P a F h) rfl,
   node P .factorPower (factorMachine P a F h) rfl,
   node P .productEntry (productEntryMachine P a F h) rfl,
   node P .productPower (productMachine P a F h) rfl,
   node P .originalGridTerm (gridTermMachine P a F h) rfl,
   node P .clearedGridSum (gridMachine P a F h) rfl,
   node P .frozenPowerTerm (frozenPowerMachine P a F h) rfl,
   node P .frozenPowerSum (frozenSumMachine P a F h) rfl,
   node P .frozenConstant (frozenConstantMachine P a F h) rfl,
   node P .frozenLower (frozenLowerMachine P a F h) rfl,
   node P .coordinateGradientProduct (coordinateMachine P a F h) rfl,
   node P .eulerSum (sumMachine P a F h) rfl,
   node P .eulerObjective (objectiveMachine P a F h) rfl,
   node P .eulerLower (lowerMachine P a F h) rfl]

theorem codes_nodup (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : ((nodes P a F h ha).map PhaseNode.code).Nodup := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List ℕ).Nodup
  decide

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : Machine := phaseDispatch (nodes P a F h ha) zero

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : IntegralMixedVirtualContextLowerModelBits.Matches P F answer)
    (hc : IntegralMixedVirtualContextLowerReplyBits.Callbacks P F answer) :
    Correct (machine P a F h ha) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  have HL := IntegralMixedVirtualContextLowerModelBits.low_matches P F answer hm
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact original_correct P a F h ha answer
  · exact IntegralMixedVirtualContextStageReplyBits.derivative_correct P a F h g answer HL
  · exact IntegralMixedVirtualContextReplyBits.height_correct_of_callbacks P a F answer hc.toCallbacks
  · exact IntegralMixedVirtualContextStageReplyBits.monomial_correct P a F h g answer HL hc.toCallbacks
  · exact IntegralMixedVirtualContextStageReplyBits.factor_correct P a F h g answer HL
  · exact IntegralMixedVirtualContextStageReplyBits.entry_correct P a F h g answer HL
  · exact IntegralMixedVirtualContextStageReplyBits.product_correct P a F h g answer HL
  · exact IntegralMixedVirtualContextStageReplyBits.term_correct P a F h answer HL
  · exact IntegralMixedVirtualContextStageReplyBits.grid_correct P a F h g answer HL
  · exact IntegralMixedVirtualContextLowerReplyBits.frozenPower_correct P a F h g answer hm
  · exact IntegralMixedVirtualContextLowerReplyBits.frozenSum_correct P a F h g answer hm
  · exact IntegralMixedVirtualContextLowerReplyBits.frozenConstant_correct P a F h answer hm hc
  · exact IntegralMixedVirtualContextLowerReplyBits.frozenLower_correct P a F h answer hm
  · exact IntegralMixedVirtualContextLowerReplyBits.coordinate_correct P a F h g answer hm
  · exact IntegralMixedVirtualContextLowerReplyBits.sum_correct P a F h g answer hm
  · exact IntegralMixedVirtualContextLowerReplyBits.objective_correct P a F h answer hm
  · exact IntegralMixedVirtualContextLowerReplyBits.lower_correct P a F h answer hm

end LeanCanny.Algebra.IntegralMixedVirtualContextLowerDispatcherBits
