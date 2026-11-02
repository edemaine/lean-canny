/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutParentInterpretation
public import LeanCanny.Encoding.IntegralFramedCutNativeValidity
/-! # Native coefficient guards construct actual selected-cut validity

The parent embedding is constructed from the complete successor vertex;
no homomorphism, relative-validity witness or degree agreement is input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutAcceptedValidity
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem exists_valid_and_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hFpos : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hg : IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w)) :
    ∃ φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
        (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val
          (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i.succ)^
            UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
              (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c))
              ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i) ∧
      IntegralMixedRelativeCuts.Valid ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ∧
      ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c))).map φ.toRingHom).natDegree=
          (family P D H).degree (IntegralMixedVirtualTaskBits.saved P c) := by
  obtain ⟨φ,hφ⟩:=IntegralFramedCutParentInterpretation.exists_interpretation P D H L F C hs c w hv ha
  exact ⟨φ,hφ,IntegralFramedCutNativeValidity.valid_and_degree P D H L F C hs hFpos hf c w hv ha φ hφ hg⟩

end LeanCanny.Encoding.IntegralFramedCutAcceptedValidity
