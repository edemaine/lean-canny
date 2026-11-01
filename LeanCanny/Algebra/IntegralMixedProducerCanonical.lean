/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedProducerActualCases
/-! # Canonical residues for the unified producer leading and companion values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] IntegralMixedIntegerProducerBits.leadingValue
  IntegralMixedPhysicalProducerLeadingBits.value IntegralMixedNormalizationTopBits.leadingValue
  IntegralMixedIntegerProducerBits.companionValue IntegralMixedPhysicalCompanionBits.companionValue
  IntegralMixedNormalizedCompanionBits.companionValue

theorem leading_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = leading P D q := by
  unfold leading
  split_ifs
  · unfold IntegralMixedIntegerProducerBits.leadingValue
    exact ⟨_, rfl⟩
  · exact IntegralMixedPhysicalProducerLeadingBits.canonical P (IntegralMixedPhysicalCompanionBits.fullFamily P D) q
  · exact IntegralMixedNormalizationTopBits.leadingValue_canonical P (IntegralMixedNormalizedCompanionBits.fullFamily P D) q

theorem companion_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = companion P D q := by
  unfold companion
  split_ifs
  · exact IntegralMixedIntegerProducerBits.companionValue_canonical P D q
  · exact IntegralMixedPhysicalCompanionBits.companionValue_canonical P (IntegralMixedPhysicalCompanionBits.fullFamily P D) q
  · exact IntegralMixedNormalizedCompanionBits.companionValue_canonical P (IntegralMixedNormalizedCompanionBits.fullFamily P D) q

end LeanCanny.Algebra.IntegralMixedProducerActualBits
