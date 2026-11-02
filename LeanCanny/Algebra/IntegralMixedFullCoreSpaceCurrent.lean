/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCoreSpace
/-! # Scalar and producer callbacks close against one current native model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullCoreSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q →
    (IntegralMixedRoutineTaskBits.routine P q = 0 ∨ IntegralMixedRoutineTaskBits.routine P q = 1 ∨ IntegralMixedRoutineTaskBits.routine P q = 6) →
      answer q = (machine P a D h).model q

theorem scalar_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedFullScalarBits.Matches P a D h.scalar answer := by
  intro q hv hr _ _
  exact (hm q hv (Or.inl hr)).trans (model_scalar P a D h q hr)

theorem algebra_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedFullAlgebraSpaceBits.Matches P a D h.algebra answer := by
  intro q hv hr
  exact (hm q hv (Or.inr hr)).trans (model_algebra P a D h q (by rcases hr with hr | hr <;> omega))

theorem producer_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedProducerActualBits.Matches P D answer :=
  IntegralMixedFullProducerSpaceBits.producer_matches P a D h.algebra.producer answer
    (IntegralMixedFullAlgebraSpaceBits.producer_matches P a D h.algebra answer (algebra_matches P a D h answer hm))

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q)))
    (hn : IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (IntegralMixedFullHistoryFamilyBits.family P D) (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedFullScalarBits.correct_of_matches P a D h.scalar _ (producer_matches P a D h _ hm) (scalar_matches P a D h _ hm)
    · intro q _
      exact IntegralMixedFullScalarBits.machine_selected P a D h.scalar q
  · exact IntegralMixedFullAlgebraSpaceBits.correct P a D h.algebra x (algebra_matches P a D h _ hm)
      (IntegralMixedFullScalarBits.physical_matches P a D h.scalar _ (scalar_matches P a D h _ hm))
      (IntegralMixedFullScalarBits.virtual_matches P a D h.scalar _ (scalar_matches P a D h _ hm)) hn

end LeanCanny.Algebra.IntegralMixedFullCoreSpaceBits
