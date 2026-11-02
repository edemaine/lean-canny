/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutCommonParent
public import LeanCanny.Encoding.IntegralFramedCutGuardSemantics
/-! # The native finite guards prove actual relative validity and degree

All indexed probes specialize through one fixed homomorphism interpreted
by the same successor tail. Higher coefficients are read before truncation.
The finite original scalar radix bounds every lower factor coefficient.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutNativeValidity
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedCutCoefficientTest.value

private theorem choice_eq (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root)
  (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
  (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
    (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val
      (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i.succ)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
          (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c))
          ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i)

include hφ in
theorem zero_iff (e k : ℕ) (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c)) :
    FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w) e k ↔
      φ ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
        (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) k)).coeff e)=0 := by
  rw [IntegralFramedCutFiniteGuards.coefficient_zero_iff P D H L F C hs hFpos hf c w hv]
  rw [IntegralFramedCutCommonParent.evaluation P D H L F C hs c ha e k he hk _ φ hφ]

include hφ in
theorem coefficientGuards
    (hg : IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w)) :
    IntegralMixedRelativeCuts.CoefficientGuards
      ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c)) := by
  let G:=family P D H
  let key:=IntegralMixedVirtualTaskBits.saved P c
  have HN:=G.scalar_cap key
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
  have HK:IntegralMixedRawKindBits.choice G key≤2^P.width (RankedHistoryTask.root c) :=
    (IntegralMixedRawKindBits.choice_le G key).trans HN
  have HD:G.degree key≤2^P.width (RankedHistoryTask.root c) := (G.degree_bound key).trans HN
  have HG :
      (∀ k<IntegralMixedRawKindBits.choice G key,∀ e<2^P.width (RankedHistoryTask.root c)+1,
        FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w) e k) ∧
      ¬FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w)
        (G.degree key) (IntegralMixedRawKindBits.choice G key) ∧
      (∀ e<2^P.width (RankedHistoryTask.root c)+1,G.degree key<e→
        FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w) e
          (IntegralMixedRawKindBits.choice G key)) ∧
      (IntegralFramedCutFiniteGuards.head P D H L F C hs (pair c w)≠InfinitesimalSign.encode 0 ∨
        FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w) 0
          (IntegralMixedRawKindBits.choice G key)) := by
    simpa only [IntegralFramedCutFiniteGuards.Guards,FiniteCoefficientSignScan.Guards,
      IntegralFramedCutFiniteGuards.choice,IntegralFramedCutFiniteGuards.degree,IntegralFramedCutFiniteGuards.cap,pairFst_pair] using hg
  rcases HG with ⟨hLower,hLeading,hHigher,_⟩
  refine ⟨?_,?_,?_⟩
  · intro k hk e he
    have hk' : k<IntegralMixedRawKindBits.choice G key := by rw [choice_eq]; exact hk
    have HE:=(zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ e k (he.trans HN) (hk'.le.trans HK)).mp
      (hLower k hk' e (Nat.lt_succ_of_le (he.trans HN)))
    rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hk] at HE
    exact HE
  · intro hz
    apply hLeading
    apply (zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ (G.degree key)
      (IntegralMixedRawKindBits.choice G key) HD HK).mpr
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]
    exact hz
  · intro e he hcap
    have HE:=(zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ e
      (IntegralMixedRawKindBits.choice G key) (hcap.trans HN) HK).mp
      (hHigher e (Nat.lt_succ_of_le (hcap.trans HN)) he)
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self] at HE
    exact HE

include hφ in
theorem valid_and_degree
    (hg : IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w)) :
    IntegralMixedRelativeCuts.Valid ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) φ ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)) ∧
      ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c))).map φ.toRingHom).natDegree=
          (family P D H).degree (IntegralMixedVirtualTaskBits.saved P c) := by
  have HC:=coefficientGuards P D H L F C hs hFpos hf c w hv ha φ hφ hg
  exact ⟨IntegralMixedRelativeCuts.coefficientGuards_valid _ _ _ _ _ _ HC,
    IntegralMixedRelativeCuts.coefficientGuards_degree _ _ _ _ _ _ HC⟩

end LeanCanny.Encoding.IntegralFramedCutNativeValidity
