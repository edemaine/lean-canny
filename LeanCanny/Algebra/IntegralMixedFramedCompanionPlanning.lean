/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQuerySpace
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanning
/-! # Budget planning preserves the actual creating source

Only task height and modulus bounds change. The scalar horizon, basis width,
literal source-framed instructions and all creating polynomials remain equal.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits

theorem source_planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) :
    source (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C)=source P D H := by
  rfl

theorem value_planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (q : List Bool) :
    PaddedIntegralGeneratorSource.value
      (source (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C)) q=
    PaddedIntegralGeneratorSource.value (source P D H) q := by
  rw [source_planned]

theorem representable_planned (P : Parameters) (L F C : List Bool → ℕ) (q : List Bool)
    (hb : IntegralMixedFramedCompanionQueryBits.sourceBirth P q<P.cap (IntegralMixedFramedCompanionQueryBits.root q))
    (hm : IntegralMixedFramedCompanionQueryBits.callerModulus q≤P.modulusBound (IntegralMixedFramedCompanionQueryBits.root q)) :
    IntegralMixedFramedCompanionQueryBits.Representable (planned P L F C) q := by
  refine ⟨hb,?_⟩
  exact hm.trans ((planned_preserves_modulus P L F C _).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.2.2)

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
