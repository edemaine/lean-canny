/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeDispatcher
/-! # Current-Q seven-routine arithmetic closes its own current model in polynomial space -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → answer q = (machine P a D H h).model q

theorem component_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer)
    (r : Fin 7) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = r.val) : answer q = (component P a D H h r).model q :=
  (hm q hv).trans (model_component P a D H h r q hr)

theorem scalar_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedCurrentQScalarBits.Matches P a D H h.scalar answer := by
  intro q hv hr hx hp
  have HE := component_matches P a D H h answer hm 0 q hv hr
  simpa only [component] using HE

theorem critical_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedCriticalBits.Matches P a D H h.critical answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 1 q hv hr
  simpa only [component] using HE

theorem entry_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedEntryBits.Matches P a D H h.critical answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 2 q hv hr
  simpa only [component] using HE

theorem determinant_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedDeterminantBits.Matches P a D H h.critical answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 3 q hv hr
  simpa only [component] using HE

theorem raw_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedNormalizationBits.RawMatches P a D H h.normalization answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 4 q hv hr
  simpa only [component, IntegralMixedFramedNormalizationBits.rawMachine] using HE

theorem normalization_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedNormalizationBits.Matches P a D H h.normalization answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 5 q hv hr
  simpa only [component] using HE

theorem producer_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedProducerBits.Matches P a D H h.producer answer := by
  intro q hv hr
  have HE := component_matches P a D H h answer hm 6 q hv hr
  simpa only [component] using HE

theorem producer_actual (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedProducerActualBits.Matches P D H answer :=
  IntegralMixedFramedProducerBits.producer_matches P a D H h.producer answer (producer_matches P a D H h answer hm)

theorem scalar_semantic (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) (hm : Matches P a D H h answer) :
    IntegralMixedFramedScalarModelBits.Matches P D H answer :=
  IntegralMixedFramedCurrentQScalarBits.semantic_matches P a D H h.scalar answer (scalar_matches P a D H h answer hm)

end LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

theorem component_canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (component P a D H h r).model q := by
  fin_cases r
  · exact IntegralMixedFramedCurrentQScalarBits.canonical P a D H h.scalar q
  · exact IntegralMixedFramedCriticalBits.canonical P a D H h.critical q
  · exact IntegralMixedFramedEntryBits.canonical P a D H h.critical q
  · exact IntegralMixedFramedDeterminantBits.canonical P a D H h.critical q
  · exact IntegralMixedFramedNormalizationBits.raw_canonical P a D H h.normalization q
  · exact IntegralMixedFramedNormalizationBits.canonical P a D H h.normalization q
  · exact IntegralMixedFramedProducerBits.canonical P a D H h.producer q

attribute [local irreducible] component

private theorem dispatch_canonical {code : List Bool → ℕ} (ns : List (PhaseNode code))
    (fallback : Machine) (m : ℕ) (q : List Bool)
    (hf : ∃ z : ZMod m, residueBits z = fallback.model q)
    (hn : ∀ n ∈ ns, ∃ z : ZMod m, residueBits z = n.machine.model q) :
    ∃ z : ZMod m, residueBits z = (phaseDispatch ns fallback).model q := by
  induction ns with
  | nil => exact hf
  | cons n ns ih =>
    change ∃ z : ZMod m, residueBits z = if n.machine.selected q then n.machine.model q else (phaseDispatch ns fallback).model q
    split_ifs
    · exact hn n List.mem_cons_self
    · exact ih (fun n hn' => hn n (List.mem_cons_of_mem _ hn'))

theorem canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D H h).model q := by
  apply dispatch_canonical _ _ _ q ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  intro n hn
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact component_canonical P a D H h _ q

end LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

structure Bounds (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : Prop where
  original : IntegralMixedFramedStepHeight.FamilyInputs P D h.normalization.nodes h.normalization.factor h.normalization.seed
  factor : ∀ root, 1 ≤ h.normalization.factor root
  fallback : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P D H h.normalization.nodes h.normalization.seed key
  modulus : ∀ root, IntegralMixedFramedNormalizationBits.requiredModulus P h.normalization.nodes h.normalization.factor h.normalization.seed root ≤ P.modulusBound root

theorem component_correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D H h (fun q => residueBits (x q)))
    (r : Fin 7) : Correct (component P a D H h r) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  have HS := scalar_matches P a D H h _ hm
  have HC := critical_matches P a D H h _ hm
  have HP := producer_actual P a D H h _ hm
  have HE := entry_matches P a D H h _ hm
  have HD := determinant_matches P a D H h _ hm
  have HR := raw_matches P a D H h _ hm
  have HN := normalization_matches P a D H h _ hm
  have HSem := scalar_semantic P a D H h _ hm
  fin_cases r
  · exact IntegralMixedFramedCurrentQScalarBits.correct_of_matches P a D H h.scalar _ HP HS
  · exact IntegralMixedFramedScalarModelBits.critical_correct P a D H h.critical x HC HSem
  · exact IntegralMixedFramedEntryBits.correct P a D H h.critical _ HC HSem HE
  · exact IntegralMixedFramedDeterminantBits.correct P a D H h.critical x HE HD
  · exact IntegralMixedFramedNormalizationBits.raw_correct P a D H h.normalization x HR
      (IntegralMixedFramedCriticalBits.virtual_matches P a D H h.critical _ HC)
      (IntegralMixedFramedProducerActualBits.bank_replies P D H _ HP)
      (IntegralMixedFramedDeterminantBits.gram_matches P a D H h.critical _ HD)
      (IntegralMixedFramedDeterminantBits.psc_matches P a D H h.critical _ HD)
  · exact IntegralMixedFramedNormalizationBits.correct P a D H h.normalization hb.original hb.factor hb.fallback hb.modulus x HN HR
  · exact IntegralMixedFramedProducerBits.correct P a D H h.producer x (producer_matches P a D H h _ hm)
      (IntegralMixedFramedCriticalBits.physical_matches P a D H h.critical _ HC)
      (IntegralMixedFramedCurrentQScalarBits.physical_matches P a D H h.scalar _ HS)
      (IntegralMixedFramedNormalizationBits.producer_matches P a D H h.normalization _ HN)

theorem component_selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) (q : List Bool) : (component P a D H h r).selected q = true := by
  fin_cases r
  · exact IntegralMixedFramedCurrentQScalarBits.machine_selected P a D H h.scalar q
  · exact IntegralMixedFramedCriticalBits.selected P a D H h.critical q
  · exact IntegralMixedFramedEntryBits.selected P a D H h.critical q
  · exact IntegralMixedFramedDeterminantBits.selected P a D H h.critical q
  · exact IntegralMixedFramedNormalizationBits.raw_selected P a D H h.normalization q
  · exact IntegralMixedFramedNormalizationBits.selected P a D H h.normalization q
  · exact IntegralMixedFramedProducerBits.selected P a D H h.producer q

attribute [local irreducible] component

theorem correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D H h (fun q => residueBits (x q))) :
    Correct (machine P a D H h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro n hn
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply withGuard_correct
    · exact component_correct P a D H h hb x hm _
    · intro q _; exact component_selected P a D H h _ q

end LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

noncomputable def residue (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) : ZMod (modulus P q) :=
  Classical.choose (canonical P a D H h q)
theorem residue_value (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    residueBits (residue P a D H h q) = (machine P a D H h).model q := Classical.choose_spec (canonical P a D H h q)

theorem correct_residue (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h) :
    Correct (machine P a D H h) (fun q => residueBits (residue P a D H h q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D H h hb (residue P a D H h) (fun q _ => residue_value P a D H h q)

theorem residue_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h) : SpaceFunction (fun q => residueBits (residue P a D H h q)) :=
  IntegralMixedNativeCompilerBits.evaluator P a (machine P a D H h) (residue P a D H h)
    (correct_residue P a D H h hb) (selected P a D H h) (fun q => (residue_value P a D H h q).symm)

theorem model_space (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (hb : Bounds P D H h) : SpaceFunction (machine P a D H h).model := by
  have HE : (fun q => residueBits (residue P a D H h q)) = (machine P a D H h).model := funext (residue_value P a D H h)
  rw [← HE]
  exact residue_space P a D H h hb

end LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeBits
