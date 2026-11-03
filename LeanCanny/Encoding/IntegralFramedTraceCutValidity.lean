/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutReadback
public import LeanCanny.Algebra.IntegralMixedRelativeCutFiniteGuards
/-! # Datum-indexed finite guards validate the actual selected factor -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutValidity
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutMetadata (terminal key terminal_positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
private theorem choice_eq (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (r u w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) r w)
local notation "c" => IntegralFramedTraceCutTask.task P (pair r (pair u []))
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "delta" => IntegralFramedTerminalCutTest.count P D H (key P D) c-IntegralMixedCutSource.Family.birth G parent
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv
variable (ha : IntegralMixedFramedFullCutProbeBits.Active P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))
  (hfit : (family P D H).birth (IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))≤
    IntegralFramedTerminalCutTest.count P D H (key P D) (IntegralFramedTraceCutTask.task P (pair r (pair u []))))
  (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))).sampler.scalarPrefix.basis.generator i)=
    IntegralFramedCompleteSuffix.joint P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv
      (i.val+(IntegralFramedTerminalCutTest.count P D H (key P D) (IntegralFramedTraceCutTask.task P (pair r (pair u [])))-
        (family P D H).birth (IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))))^
    UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))
      (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P (pair r (pair u [])))))
      ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P (pair r (pair u []))))) i)

include hφ hfit ha hv in
theorem coefficientGuards
    (hg : IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (pair (pair r w) u)) :
    IntegralMixedRelativeCuts.CoefficientGuards
      ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c)) := by
  let M:=family P D H
  let creator:=IntegralMixedVirtualTaskBits.saved P c
  have HN:=M.scalar_cap creator
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
  simp only [IntegralFramedTraceCutTask.task_root,pairFst_pair] at HN
  have HK:IntegralMixedRawKindBits.choice M creator≤2^P.width r :=
    (IntegralMixedRawKindBits.choice_le M creator).trans HN
  have HD:M.degree creator≤2^P.width r := (M.degree_bound creator).trans HN
  have HG :
      (∀ k<IntegralMixedRawKindBits.choice M creator,∀ e<2^P.width r+1,
        FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) e k) ∧
      ¬FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u)
        (M.degree creator) (IntegralMixedRawKindBits.choice M creator) ∧
      (∀ e<2^P.width r+1,M.degree creator<e→
        FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) e
          (IntegralMixedRawKindBits.choice M creator)) ∧
      (IntegralFramedTraceCutGuards.head P D H L F C hs (pair (pair r w) u)≠InfinitesimalSign.encode 0 ∨
        FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) 0
          (IntegralMixedRawKindBits.choice M creator)) := by
    simpa only [IntegralFramedTraceCutGuards.Guards,FiniteCoefficientSignScan.Guards,
      IntegralFramedTraceCutGuards.choice,IntegralFramedTraceCutGuards.degree,IntegralFramedTraceCutGuards.cap,
      IntegralFramedTraceCutGuards.root,IntegralFramedTraceCutGuards.parent,Function.comp_apply,
      IntegralFramedTraceCutGuards.descriptor,pairFst_pair,pairSnd_pair] using hg
  rcases HG with ⟨hLower,hLeading,hHigher,_⟩
  refine ⟨?_,?_,?_⟩
  · intro k hk e he
    have hk' : k<IntegralMixedRawKindBits.choice M creator := by rw [choice_eq]; exact hk
    have HE:=(IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha hfit φ hφ e k (he.trans HN) (hk'.le.trans HK)).mp
      (hLower k hk' e (Nat.lt_succ_of_le (he.trans HN)))
    rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hk] at HE
    exact HE
  · intro hz
    apply hLeading
    apply (IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha hfit φ hφ (M.degree creator)
      (IntegralMixedRawKindBits.choice M creator) HD HK).mpr
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]
    exact hz
  · intro e he hcap
    have HE:=(IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha hfit φ hφ e
      (IntegralMixedRawKindBits.choice M creator) (hcap.trans HN) HK).mp
      (hHigher e (Nat.lt_succ_of_le (hcap.trans HN)) he)
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self] at HE
    exact HE

include hφ hfit ha hv in
theorem valid_and_degree
    (hg : IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (pair (pair r w) u)) :
    IntegralMixedRelativeCuts.Valid ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ∧
      ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c))).map φ.toRingHom).natDegree=
          (family P D H).degree (IntegralMixedVirtualTaskBits.saved P c) := by
  have HC:=coefficientGuards P D H L F C hs hFpos hf r u w hv ha hfit φ hφ hg
  exact ⟨IntegralMixedRelativeCuts.coefficientGuards_valid _ _ _ _ _ _ HC,
    IntegralMixedRelativeCuts.coefficientGuards_degree _ _ _ _ _ _ HC⟩

end LeanCanny.Encoding.IntegralFramedTraceCutValidity
