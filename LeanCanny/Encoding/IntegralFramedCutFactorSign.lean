/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutCoefficientSign
public import LeanCanny.Algebra.IntegralMixedCutCoefficientReadback
/-! # Successor coefficient signs specialize the actual relative factor

The selected homomorphism interprets the literal old tail of the same
successor tuple. The query changes only local coefficient/choice fields.
No independent coordinate roots or absolute-norm root transport occurs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutCoefficientTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem query_active (P : Parameters) (z : List Bool) :
    IntegralMixedFramedFullCutProbeBits.Active P (query P z) ↔
      IntegralMixedFramedFullCutProbeBits.Active P (pairFst z) := by
  unfold query
  rw [IntegralMixedCutCoefficientQueryBits.query_active,pairFst_pair]

theorem factor_eval (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (c d : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (z : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)→ℝ)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (query P (pair c d)))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P (query P (pair c d)))).sampler.scalarPrefix.basis.generator i)=
      z (Fin.cast (dimension_pair P D H L F C hs c d ha) i.succ)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P (query P (pair c d)))
          (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P (query P (pair c d))))
          ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P (query P (pair c d)))) i) :
    (polynomial P D H L F C hs c d).eval₂ (Int.castRingHom ℝ) z=
      φ ((IntegralMixedRelativeCuts.factor
        ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (query P (pair c d))))
        ((family P D H).birth_bound _) ((family P D H).rule _)
        (IntegralMixedRelativeCuts.atChoice ((family P D H).rule _) ((family P D H).kind _)
          (IntegralMixedRawKindChoiceBits.requested P (query P (pair c d))))).coeff
            (get P .coefficient (query P (pair c d)))) := by
  have hqa : IntegralMixedFramedFullCutProbeBits.Active P (query P (pair c d)) :=
    (query_active P _).mpr (by simpa only [pairFst_pair] using ha)
  exact (polynomial_eval P D H L F C hs c d ha z).trans
    (IntegralMixedFramedChoiceProbeSourceBits.evaluation P D H (query P (pair c d)) hqa _ φ hφ)

end LeanCanny.Encoding.IntegralFramedCutCoefficientTest
