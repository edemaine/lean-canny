/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerNative
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Integer leading, coefficient, and companion phases share one native dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedIntegerProducerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def leadingNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) : PhaseNode phase where
  machine := leadingMachine P a D h c
  code := 0
  selected_phase q hs := ((selected_iff P .originalCoefficient q).mp hs).2.2.1

noncomputable def coefficientNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (c : OriginalCells P D) : PhaseNode phase where
  machine := coefficientMachine P a D c
  code := 25
  selected_phase q hs := ((selected_iff P .criticalCoefficient q).mp hs).2.2.1

noncomputable def companionNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) : PhaseNode phase where
  machine := companionMachine P a D h
  code := 26
  selected_phase q hs := ((selected_iff P .companion q).mp hs).2.2.1

noncomputable def nodes (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) : List (PhaseNode phase) :=
  [leadingNode P a D h c, coefficientNode P a D c, companionNode P a D h]

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) : Machine := phaseDispatch (nodes P a D h c) zero

theorem nodes_distinct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) : ((nodes P a D h c).map PhaseNode.code).Nodup := by change [0, 25, 26].Nodup; decide

theorem model_leading (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (q : List Bool) (hs : selected P .originalCoefficient q = true) :
    (machine P a D h c).model q = leadingValue P D q :=
  phaseDispatch_model_selected _ _ q (leadingNode P a D h c) (nodes_distinct P a D h c) List.mem_cons_self hs

theorem model_coefficient (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (q : List Bool) (hs : selected P .criticalCoefficient q = true) :
    (machine P a D h c).model q = coefficientValue P D q :=
  phaseDispatch_model_selected _ _ q (coefficientNode P a D c) (nodes_distinct P a D h c)
    (List.mem_cons_of_mem _ List.mem_cons_self) hs

theorem model_companion (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (q : List Bool) (hs : selected P .companion q = true) :
    (machine P a D h c).model q = companionValue P D q :=
  phaseDispatch_model_selected _ _ q (companionNode P a D h) (nodes_distinct P a D h c)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hs

theorem machine_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (q : List Bool) : (machine P a D h c).selected q = true := by
  change (selected P .originalCoefficient q || (selected P .criticalCoefficient q || (selected P .companion q || true))) = true
  rw [Bool.or_true, Bool.or_true, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : CoefficientMatches P D (fun q => residueBits (x q))) (hl : LeadingMatches P D (fun q => residueBits (x q))) :
    Correct (machine P a D h c) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact leaf_correct P .originalCoefficient a (leadingValue P D) (leadingValue_FP P a D h c) _
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact leaf_correct P .criticalCoefficient a (coefficientValue P D) (coefficientValue_FP P a D c) _
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact companion_correct P a D h x hm hl
      · cases hb

end LeanCanny.Algebra.IntegralMixedIntegerProducerDispatcherBits
