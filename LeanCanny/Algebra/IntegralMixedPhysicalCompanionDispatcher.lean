/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionNative
/-! # Physical producer and companion phases share one native model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCompanionDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalCompanionBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def leadingNode (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : PhaseNode phase where
  machine := IntegralMixedPhysicalProducerLeadingBits.machine P a F h
  code := 0
  selected_phase q hs := ((IntegralMixedPhysicalProducerLeadingBits.selected_iff P q).mp hs).2.2.1

noncomputable def companionNode (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : PhaseNode phase where
  machine := companionStage P a F h
  code := 26
  selected_phase q hs := ((selected_iff P q).mp hs).2.2.1

noncomputable def nodes (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : List (PhaseNode phase) :=
  [leadingNode P a F h, companionNode P a F h]

noncomputable def machine (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : Machine :=
  phaseDispatch (nodes P a F h) zero

theorem nodes_distinct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :
    ((nodes P a F h).map PhaseNode.code).Nodup := by change [0, 26].Nodup; decide

theorem model_leading (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (q : List Bool)
    (hs : IntegralMixedPhysicalProducerLeadingBits.selected P q = true) :
    (machine P a F h).model q = IntegralMixedPhysicalProducerLeadingBits.value P F q :=
  phaseDispatch_model_selected _ _ q (leadingNode P a F h) (nodes_distinct P a F h)
    List.mem_cons_self hs

theorem model_companion (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (q : List Bool)
    (hs : selected P q = true) :
    (machine P a F h).model q = companionValue P F q :=
  phaseDispatch_model_selected _ _ q (companionNode P a F h) (nodes_distinct P a F h)
    (List.mem_cons_of_mem _ List.mem_cons_self) hs

theorem machine_selected (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true := by
  change ((IntegralMixedPhysicalProducerLeadingBits.selected P q) || ((selected P q) || true)) = true
  rw [Bool.or_true, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : CriticalMatches P F (fun q => residueBits (x q)))
    (hl : LeadingMatches P F (fun q => residueBits (x q)))
    (hs : IntegralMixedPhysicalScalarReplyBits.Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact IntegralMixedPhysicalProducerLeadingBits.correct_of_matches P a F h x hs
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact companion_correct P a F h g x hm hl
    · cases hb

end LeanCanny.Algebra.IntegralMixedPhysicalCompanionDispatcherBits
