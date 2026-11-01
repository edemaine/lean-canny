/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalContextLowerReplies
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Native physical arithmetic dispatcher for phases zero to sixteen -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits IntegralMixedPhysicalContextBits NativeControllerBranch
open IntegralMixedPhysicalNativeLowerBits (originalScalar)
set_option backward.isDefEq.respectTransparency false

noncomputable def node (P : Parameters) (p : Phase) (M : Machine)
    (hs : M.selected = selected P p) : PhaseNode phase where
  machine := M
  code := p.code
  selected_phase q hq := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P p q).mp
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
    (ha : SpaceFunction (originalScalar P F)) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : IntegralMixedPhysicalContextLowerModelBits.Matches P F answer)
    (hc : IntegralMixedPhysicalContextLowerReplyBits.Callbacks P F answer) :
    Correct (machine P a F h ha) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  have HL := IntegralMixedPhysicalContextLowerModelBits.low_matches P F answer hm
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact original_correct P a F h ha answer
  · exact IntegralMixedPhysicalContextStageReplyBits.derivative_correct P a F h g answer HL
  · exact IntegralMixedPhysicalContextReplyBits.height_correct_of_callbacks P a F answer hc.toCallbacks
  · exact IntegralMixedPhysicalContextStageReplyBits.monomial_correct P a F h g answer HL hc.toCallbacks
  · exact IntegralMixedPhysicalContextStageReplyBits.factor_correct P a F h g answer HL
  · exact IntegralMixedPhysicalContextStageReplyBits.entry_correct P a F h g answer HL
  · exact IntegralMixedPhysicalContextStageReplyBits.product_correct P a F h g answer HL
  · exact IntegralMixedPhysicalContextStageReplyBits.term_correct P a F h answer HL
  · exact IntegralMixedPhysicalContextStageReplyBits.grid_correct P a F h g answer HL
  · exact IntegralMixedPhysicalContextLowerReplyBits.frozenPower_correct P a F h g answer hm
  · exact IntegralMixedPhysicalContextLowerReplyBits.frozenSum_correct P a F h g answer hm
  · exact IntegralMixedPhysicalContextLowerReplyBits.frozenConstant_correct P a F h answer hm hc
  · exact IntegralMixedPhysicalContextLowerReplyBits.frozenLower_correct P a F h answer hm
  · exact IntegralMixedPhysicalContextLowerReplyBits.coordinate_correct P a F h g answer hm
  · exact IntegralMixedPhysicalContextLowerReplyBits.sum_correct P a F h g answer hm
  · exact IntegralMixedPhysicalContextLowerReplyBits.objective_correct P a F h answer hm
  · exact IntegralMixedPhysicalContextLowerReplyBits.lower_correct P a F h answer hm

end LeanCanny.Algebra.IntegralMixedPhysicalLowerDispatcherBits
