/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCompleteSuffixSaved
public import LeanCanny.Encoding.IntegralFramedTerminalCutSource
/-! # The actual terminal vertex constructs the one selected parent homomorphism -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutParent
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)

include ha in
theorem exists_interpretation
    (hroot : pairFst (key c)=RankedHistoryTask.root c)
    (hfit : (family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)≤IntegralFramedTerminalCutTest.count P D H key c) :
    ∃ φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
          (i.val+(IntegralFramedTerminalCutTest.count P D H key c-(family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)))^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
            (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i := by
  have HB:=(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
  have HF : birth P c≤(family P D H).birth (key c) := by
    rw [HB] at hfit
    exact hfit
  have HR:=IntegralFramedCompleteSuffixSaved.parent_roots P D H c (key c) ha hroot HF
    (IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv)
    (IntegralFramedCompleteSuffix.terminal_roots P D H L F C hs key hpos c w hv)
  obtain ⟨φ,hφ⟩:=((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.interpret ℝ
    (fun i=>IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv (i.val+((family P D H).birth (key c)-birth P c))) HR
  have HS : (family P D H).cap (IntegralMixedVirtualTaskBits.saved P c)=IntegralMixedFramedChoiceProbeSourceBits.horizon P c := by
    unfold family
    change P.cap (pairFst (IntegralMixedVirtualTaskBits.saved P c))+1=P.cap (RankedHistoryTask.root c)+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  have HD : (family P D H).birth (key c)-birth P c=
      IntegralFramedTerminalCutTest.count P D H key c-(family P D H).birth (IntegralMixedVirtualTaskBits.saved P c) := by
    rw [HB]
    rfl
  refine ⟨φ,fun i=>?_⟩
  simpa only [HS,HD] using hφ i

end LeanCanny.Encoding.IntegralFramedTerminalCutParent
