/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutRoot
public import LeanCanny.Encoding.IntegralFramedTerminalCutRows
public import LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
public import LeanCanny.Algebra.IntegralMixedCutJointRootGuard
public import LeanCanny.Algebra.IntegralMixedCutHeadRootGuard
/-! # Actual terminal bank roots pass every datum-indexed cut guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutGuardComplete
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutMetadata (terminal key terminal_positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem self_choice (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) (IntegralMixedRawKindBits.choice G key)=G.kind key := by
  have HC : IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
    cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]
  rw [HC,IntegralMixedRelativeCuts.atChoice_self]

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
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "factor" => IntegralMixedRelativeCuts.factor old bound rule kind
local notation "M" => IntegralMixedCutSource.Family.birth G (terminal P D r)
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv
local notation "cutTuple" => (fun i : Fin (IntegralMixedCutSource.Family.birth G parent+1)=>z (Fin.val i+(M-(birth P c+1))))
local notation "bankPoint" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state G (terminal P D r))) z (M-birth P c-1)

include hv in
theorem guards (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hstage : birth P c=u.length) (hfit : birth P c<M)
    (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i)
    (hvalid : IntegralMixedRelativeCuts.Valid old bound rule φ kind)
    (hd : ((factor).map φ.toRingHom).natDegree=degree)
    (hroot : (factor).eval₂ φ.toRingHom (IntegralRelativeTruncation.jointQuotient (old).sampler.scalarPrefix factor degree cutTuple)=0) :
    IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (pair (pair r w) u) := by
  have HC : IntegralFramedTerminalCutTest.count P D H (key P D) c=M := by
    change (G).birth (key P D c)=M
    rw [IntegralFramedTraceCutMetadata.key_task,pairFst_pair]
  have Hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(IntegralFramedTerminalCutTest.count P D H (key P D) c-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) (2^(G).width parent) ((G).birth parent) i := by simpa only [HC] using hφ
  have HF : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H (key P D) c := by
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c,HC]
    exact hfit.le
  have HN:=(G).scalar_cap parent
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
  simp only [IntegralFramedTraceCutTask.task_root,pairFst_pair] at HN
  have HK : (IntegralMixedRawKindBits.choice G parent)≤2^P.width r :=
    (IntegralMixedRawKindBits.choice_le G parent).trans HN
  have HD : degree≤2^P.width r := ((G).degree_bound parent).trans HN
  obtain ⟨HLower,HNonzero⟩:=(IntegralMixedRelativeCuts.valid_iff_lower_factors old bound rule φ kind).mp hvalid
  have HG :
      (∀ j<(IntegralMixedRawKindBits.choice G parent),∀ e<2^P.width r+1,FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) e j) ∧
      ¬FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) degree (IntegralMixedRawKindBits.choice G parent) ∧
      (∀ e<2^P.width r+1,degree<e→FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) e (IntegralMixedRawKindBits.choice G parent)) ∧
      (IntegralFramedTraceCutGuards.head P D H L F C hs (pair (pair r w) u)≠InfinitesimalSign.encode 0 ∨
        FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) 0 (IntegralMixedRawKindBits.choice G parent)) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj e he
      have hj' : j<IntegralMixedRelativeCuts.choiceIndex rule kind := by simpa only [choice_eq] using hj
      have HM:=HLower j hj'
      have HC:=congrArg (fun q : Polynomial ℝ=>q.coeff e) HM
      have HZ : φ ((IntegralMixedRelativeCuts.factor old bound rule
          (IntegralMixedRelativeCuts.atChoice rule kind j)).coeff e)=0 := by
        rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hj']
        simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
      exact (IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha HF φ Hφ e j
        (by omega) (hj.le.trans HK)).mpr HZ
    · intro HZero
      have HC:=(IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha HF φ Hφ degree (IntegralMixedRawKindBits.choice G parent) HD HK).mp HZero
      rw [self_choice] at HC
      have HT : ((factor).map φ.toRingHom).coeff degree≠0 := by
        rw [←hd]
        exact Polynomial.leadingCoeff_ne_zero.mpr HNonzero
      apply HT
      simpa only [Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
    · intro e he hgt
      have HC : ((factor).map φ.toRingHom).coeff e=0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hgt)
      apply (IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha HF φ Hφ e (IntegralMixedRawKindBits.choice G parent) (by omega) HK).mpr
      rw [self_choice]
      simpa only [Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
    · by_cases HH : IntegralFramedTraceCutGuards.head P D H L F C hs (pair (pair r w) u)=InfinitesimalSign.encode 0
      · right
        have HZ:=(IntegralFramedTraceCutRoot.head_zero_iff P D H L F C hs r u w hv hstage hfit).mp HH
        have HQ:=(IntegralRelativeTruncation.jointQuotient_zero_iff (old).sampler.scalarPrefix factor degree cutTuple).mpr HZ
        have HC : φ ((factor).coeff 0)=0 := by
          simpa only [HQ,Polynomial.eval₂_at_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hroot
        apply (IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha HF φ Hφ 0 (IntegralMixedRawKindBits.choice G parent) (Nat.zero_le _) HK).mpr
        rw [self_choice]
        exact HC
      · exact Or.inl HH
  simpa only [IntegralFramedTraceCutGuards.Guards,FiniteCoefficientSignScan.Guards,IntegralFramedTraceCutGuards.choice,
    IntegralFramedTraceCutGuards.degree,IntegralFramedTraceCutGuards.cap,IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,pairFst_pair,pairSnd_pair] using HG

end LeanCanny.Encoding.IntegralFramedTraceCutGuardComplete
