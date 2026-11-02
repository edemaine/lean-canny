/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceLeaf
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Integer leading, coefficient, and companion phases share one native dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedIntegerProducerBits NativeControllerBranch
open IntegralMixedIntegerProducerSpaceBits

noncomputable def leadingNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) : PhaseNode phase where
  machine := IntegralMixedIntegerProducerSpaceBits.leaf P a .originalCoefficient (leadingValue P D) (leading_evaluator P a D h)
  code := 0
  selected_phase q hs := ((selected_iff P .originalCoefficient q).mp hs).2.2.1

noncomputable def coefficientNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) : PhaseNode phase where
  machine := IntegralMixedIntegerProducerSpaceBits.leaf P a .criticalCoefficient (coefficientValue P D) (coefficient_evaluator P a D h)
  code := 25
  selected_phase q hs := ((selected_iff P .criticalCoefficient q).mp hs).2.2.1

noncomputable def companionNode (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) : PhaseNode phase where
  machine := IntegralMixedIntegerProducerSpaceBits.leaf P a .companion (companionValue P D) (companion_evaluator P a D h)
  code := 26
  selected_phase q hs := ((selected_iff P .companion q).mp hs).2.2.1

noncomputable def nodes (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) : List (PhaseNode phase) :=
  [leadingNode P a D h, coefficientNode P a D h, companionNode P a D h]

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) : Machine := phaseDispatch (nodes P a D h) zero

theorem nodes_distinct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) : ((nodes P a D h).map PhaseNode.code).Nodup := by change [0, 25, 26].Nodup; decide

theorem model_leading (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) (q : List Bool) (hs : selected P .originalCoefficient q = true) :
    (machine P a D h).model q = leadingValue P D q :=
  phaseDispatch_model_selected _ _ q (leadingNode P a D h) (nodes_distinct P a D h) List.mem_cons_self hs

theorem model_coefficient (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) (q : List Bool) (hs : selected P .criticalCoefficient q = true) :
    (machine P a D h).model q = coefficientValue P D q :=
  phaseDispatch_model_selected _ _ q (coefficientNode P a D h) (nodes_distinct P a D h)
    (List.mem_cons_of_mem _ List.mem_cons_self) hs

theorem model_companion (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) (q : List Bool) (hs : selected P .companion q = true) :
    (machine P a D h).model q = companionValue P D q :=
  phaseDispatch_model_selected _ _ q (companionNode P a D h) (nodes_distinct P a D h)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hs

theorem machine_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) (q : List Bool) : (machine P a D h).selected q = true := by
  change (selected P .originalCoefficient q || (selected P .criticalCoefficient q || (selected P .companion q || true))) = true
  rw [Bool.or_true, Bool.or_true, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) (answer : List Bool → List Bool) :
    Correct (machine P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact IntegralMixedIntegerProducerSpaceBits.leaf_correct P a .originalCoefficient _ (leading_evaluator P a D h) answer
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact IntegralMixedIntegerProducerSpaceBits.leaf_correct P a .criticalCoefficient _ (coefficient_evaluator P a D h) answer
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact IntegralMixedIntegerProducerSpaceBits.leaf_correct P a .companion _ (companion_evaluator P a D h) answer
      · cases hb

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedIntegerProducerSpaceBits.Original P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if IntegralMixedIntegerProducerBits.selected P .originalCoefficient q then leadingValue P D q else
      if IntegralMixedIntegerProducerBits.selected P .criticalCoefficient q then coefficientValue P D q else
        if IntegralMixedIntegerProducerBits.selected P .companion q then companionValue P D q else []
  split_ifs
  · exact ⟨_, rfl⟩
  · unfold coefficientValue
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  · exact companionValue_canonical P D q
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

end LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceDispatcherBits
