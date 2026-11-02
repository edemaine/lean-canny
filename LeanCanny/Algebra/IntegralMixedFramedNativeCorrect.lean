/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeCurrent
/-! # One current model closes all seven framed arithmetic routines -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeBits
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
  · exact IntegralMixedFramedFullScalarBits.correct_of_matches P a D H h.scalar _ HP HS
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
      (IntegralMixedFramedFullScalarBits.physical_matches P a D H h.scalar _ HS)
      (IntegralMixedFramedNormalizationBits.producer_matches P a D H h.normalization _ HN)

theorem component_selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) (q : List Bool) : (component P a D H h r).selected q = true := by
  fin_cases r
  · exact IntegralMixedFramedFullScalarBits.machine_selected P a D H h.scalar q
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

end LeanCanny.Algebra.IntegralMixedFramedNativeBits
