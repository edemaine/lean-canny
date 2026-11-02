/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutParent
public import LeanCanny.Encoding.IntegralFramedTerminalCutValidity
/-! # Accepted terminal guards construct actual relative validity

The parent homomorphism is obtained from the one complete terminal tuple.
Neither a parent root, a relative-validity proof nor specialized degree
agreement is a caller premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutAcceptedValidity
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)

include ha in
theorem exists_valid_and_degree
    (hroot : pairFst (key c)=RankedHistoryTask.root c)
    (hfit : (family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)≤IntegralFramedTerminalCutTest.count P D H key c)
    (hg : IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w)) :
    ∃ φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
          (i.val+(IntegralFramedTerminalCutTest.count P D H key c-(family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)))^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
            (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i) ∧
      IntegralMixedRelativeCuts.Valid ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound _) ((family P D H).rule _) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ∧
      ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound _) ((family P D H).rule _) ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c))).map φ.toRingHom).natDegree=
          (family P D H).degree (IntegralMixedVirtualTaskBits.saved P c) := by
  obtain ⟨φ,hφ⟩:=IntegralFramedTerminalCutParent.exists_interpretation P D H L F C hs key hpos c w hv ha hroot hfit
  exact ⟨φ,hφ,IntegralFramedTerminalCutValidity.valid_and_degree P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ hg⟩

end LeanCanny.Encoding.IntegralFramedTerminalCutAcceptedValidity
