/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerFamilySpace
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Generic original-integer phases over actual retained prefix families -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedIntegerProducerBits NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
attribute [local irreducible] PaddedIntegralGeneratorFinBits.Family.matrix

theorem companionValue_canonical (P : Parameters) (F : Family) (p : List Bool → Polynomial ℤ) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z=companionValue P F p q := by
  unfold companionValue PaddedIntegralGeneratorFinBits.Family.value
  exact ⟨_,rfl⟩

attribute [local irreducible] companionValue leadingValue coefficientValue rawScalar

noncomputable def leadingNode (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) : PhaseNode phase where
  machine := IntegralMixedIntegerProducerSpaceBits.leaf P a .originalCoefficient (leadingValue P p) (leading_evaluator P a F h p hp)
  code := 0
  selected_phase q hs := ((selected_iff P .originalCoefficient q).mp hs).2.2.1

noncomputable def coefficientNode (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) : PhaseNode phase where
  machine := IntegralMixedIntegerProducerSpaceBits.leaf P a .criticalCoefficient (coefficientValue P F p) (coefficient_evaluator P a F h p hp)
  code := 25
  selected_phase q hs := ((selected_iff P .criticalCoefficient q).mp hs).2.2.1

noncomputable def companionNode (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) : PhaseNode phase where
  machine := IntegralMixedIntegerProducerSpaceBits.leaf P a .companion (companionValue P F p) (companion_evaluator P a F h p hp)
  code := 26
  selected_phase q hs := ((selected_iff P .companion q).mp hs).2.2.1

noncomputable def nodes (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) : List (PhaseNode phase) :=
  [leadingNode P a F h p hp, coefficientNode P a F h p hp, companionNode P a F h p hp]

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) : Machine := phaseDispatch (nodes P a F h p hp) zero

theorem nodes_distinct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) : ((nodes P a F h p hp).map PhaseNode.code).Nodup := by change [0, 25, 26].Nodup; decide

theorem model_leading (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) (q : List Bool) (hs : selected P .originalCoefficient q = true) :
    (machine P a F h p hp).model q = leadingValue P p q :=
  phaseDispatch_model_selected _ _ q (leadingNode P a F h p hp) (nodes_distinct P a F h p hp) List.mem_cons_self hs

theorem model_coefficient (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) (q : List Bool) (hs : selected P .criticalCoefficient q = true) :
    (machine P a F h p hp).model q = coefficientValue P F p q :=
  phaseDispatch_model_selected _ _ q (coefficientNode P a F h p hp) (nodes_distinct P a F h p hp)
    (List.mem_cons_of_mem _ List.mem_cons_self) hs

theorem model_companion (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) (q : List Bool) (hs : selected P .companion q = true) :
    (machine P a F h p hp).model q = companionValue P F p q :=
  phaseDispatch_model_selected _ _ q (companionNode P a F h p hp) (nodes_distinct P a F h p hp)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hs

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) (q : List Bool) : (machine P a F h p hp).selected q = true := by
  change (selected P .originalCoefficient q || (selected P .criticalCoefficient q || (selected P .companion q || true))) = true
  rw [Bool.or_true, Bool.or_true, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) (answer : List Bool → List Bool) :
    Correct (machine P a F h p hp) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact IntegralMixedIntegerProducerSpaceBits.leaf_correct P a .originalCoefficient _ (leading_evaluator P a F h p hp) answer
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact IntegralMixedIntegerProducerSpaceBits.leaf_correct P a .criticalCoefficient _ (coefficient_evaluator P a F h p hp) answer
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact IntegralMixedIntegerProducerSpaceBits.leaf_correct P a .companion _ (companion_evaluator P a F h p hp) answer
      · cases hb

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ)
    (hp : Original P p) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h p hp).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if IntegralMixedIntegerProducerBits.selected P .originalCoefficient q then leadingValue P p q else
      if IntegralMixedIntegerProducerBits.selected P .criticalCoefficient q then coefficientValue P F p q else
        if IntegralMixedIntegerProducerBits.selected P .companion q then companionValue P F p q else []
  split_ifs
  · unfold leadingValue
    exact ⟨_, rfl⟩
  · unfold coefficientValue
    split_ifs
    · unfold rawScalar
      exact ⟨_, rfl⟩
    · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  · exact companionValue_canonical P F p q
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

end LeanCanny.Algebra.IntegralMixedIntegerFamilyBits
