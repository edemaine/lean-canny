/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutCommonParent
public import LeanCanny.Encoding.IntegralFramedTerminalCutGuards
/-! # Finite terminal guards imply actual relative validity and specialized degree -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutValidity
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedTerminalCutTest.value IntegralFramedTerminalCutGuards.head

private theorem choice_eq (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "delta" => IntegralFramedTerminalCutTest.count P D H key c-IntegralMixedCutSource.Family.birth G parent
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
local notation "sample" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv)
local notation "T" => IntegralFramedTerminalCutTest.source P D H L F C hs key hpos hFpos hf

variable (hfit : (family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)≤IntegralFramedTerminalCutTest.count P D H key c)
  (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
    IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
      (i.val+(IntegralFramedTerminalCutTest.count P D H key c-(family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)))^
    UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
      (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i)

include hφ hfit ha hv in
theorem coefficientGuards
    (hg : IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w)) :
    IntegralMixedRelativeCuts.CoefficientGuards
      ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c)) := by
  let M:=family P D H
  let creator:=IntegralMixedVirtualTaskBits.saved P c
  have HN:=M.scalar_cap creator
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
  have HK:IntegralMixedRawKindBits.choice M creator≤2^P.width (RankedHistoryTask.root c) :=
    (IntegralMixedRawKindBits.choice_le M creator).trans HN
  have HD:M.degree creator≤2^P.width (RankedHistoryTask.root c) := (M.degree_bound creator).trans HN
  have HG :
      (∀ k<IntegralMixedRawKindBits.choice M creator,∀ e<2^P.width (RankedHistoryTask.root c)+1,
        FiniteCoefficientSignScan.Zero (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos) (pair c w) e k) ∧
      ¬FiniteCoefficientSignScan.Zero (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos) (pair c w)
        (M.degree creator) (IntegralMixedRawKindBits.choice M creator) ∧
      (∀ e<2^P.width (RankedHistoryTask.root c)+1,M.degree creator<e→
        FiniteCoefficientSignScan.Zero (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos) (pair c w) e
          (IntegralMixedRawKindBits.choice M creator)) ∧
      (IntegralFramedTerminalCutGuards.head P D H L F C hs key hpos (pair c w)≠InfinitesimalSign.encode 0 ∨
        FiniteCoefficientSignScan.Zero (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos) (pair c w) 0
          (IntegralMixedRawKindBits.choice M creator)) := by
    simpa only [IntegralFramedTerminalCutGuards.Guards,FiniteCoefficientSignScan.Guards,
      IntegralFramedCutFiniteGuards.choice,IntegralFramedCutFiniteGuards.degree,IntegralFramedCutFiniteGuards.cap,pairFst_pair] using hg
  rcases HG with ⟨hLower,hLeading,hHigher,_⟩
  refine ⟨?_,?_,?_⟩
  · intro k hk e he
    have hk' : k<IntegralMixedRawKindBits.choice M creator := by rw [choice_eq]; exact hk
    have HE:=(IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ e k (he.trans HN) (hk'.le.trans HK)).mp
      (hLower k hk' e (Nat.lt_succ_of_le (he.trans HN)))
    rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hk] at HE
    exact HE
  · intro hz
    apply hLeading
    apply (IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ (M.degree creator)
      (IntegralMixedRawKindBits.choice M creator) HD HK).mpr
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]
    exact hz
  · intro e he hcap
    have HE:=(IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ e
      (IntegralMixedRawKindBits.choice M creator) (hcap.trans HN) HK).mp
      (hHigher e (Nat.lt_succ_of_le (hcap.trans HN)) he)
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self] at HE
    exact HE

include hφ hfit ha hv in
theorem valid_and_degree
    (hg : IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w)) :
    IntegralMixedRelativeCuts.Valid ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ∧
      ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c))).map φ.toRingHom).natDegree=
          (family P D H).degree (IntegralMixedVirtualTaskBits.saved P c) := by
  have HC:=coefficientGuards P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ hg
  exact ⟨IntegralMixedRelativeCuts.coefficientGuards_valid _ _ _ _ _ _ HC,
    IntegralMixedRelativeCuts.coefficientGuards_degree _ _ _ _ _ _ HC⟩

end LeanCanny.Encoding.IntegralFramedTerminalCutValidity
