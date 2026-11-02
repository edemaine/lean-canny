/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutAcceptedRoot
/-! # Actual full-factor roots pass every finite terminal cut guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutGuardComplete
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedTerminalCutTest.value IntegralFramedTerminalCutGuards.head

private theorem choice_eq (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]
private theorem self_choice (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) (IntegralMixedRawKindBits.choice G key)=G.kind key := by
  rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]

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
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "factor" => IntegralMixedRelativeCuts.factor old bound rule kind
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
local notation "cutTuple" => (fun i : Fin (IntegralMixedCutSource.Family.birth G parent+1)=>
  z (Fin.val i+(IntegralMixedCutSource.Family.birth G (key c)-(birth P c+1))))
local notation "sample" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv)
local notation "chosen" => IntegralMixedRawKindBits.choice G parent
local notation "sign" => IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos

include ha in
theorem guards (hfit : birth P c<(G).birth (key c))
    (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+((G).birth (key c)-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i)
    (hvalid : IntegralMixedRelativeCuts.Valid old bound rule φ kind)
    (hd : ((factor).map φ.toRingHom).natDegree=degree)
    (hroot : (factor).eval₂ φ.toRingHom (IntegralRelativeTruncation.jointQuotient (old).sampler.scalarPrefix factor degree cutTuple)=0) :
    IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w) := by
  have HF : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H key c := by
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c]
    exact hfit.le
  have HN:=(G).scalar_cap parent
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
  have HK : chosen≤2^P.width (RankedHistoryTask.root c) :=
    (IntegralMixedRawKindBits.choice_le G parent).trans HN
  have HD : degree≤2^P.width (RankedHistoryTask.root c) := ((G).degree_bound parent).trans HN
  obtain ⟨HLower,HNonzero⟩:=(IntegralMixedRelativeCuts.valid_iff_lower_factors old bound rule φ kind).mp hvalid
  have HG :
      (∀ j<chosen,∀ e<2^P.width (RankedHistoryTask.root c)+1,FiniteCoefficientSignScan.Zero sign (pair c w) e j) ∧
      ¬FiniteCoefficientSignScan.Zero sign (pair c w) degree chosen ∧
      (∀ e<2^P.width (RankedHistoryTask.root c)+1,degree<e→FiniteCoefficientSignScan.Zero sign (pair c w) e chosen) ∧
      (IntegralFramedTerminalCutGuards.head P D H L F C hs key hpos (pair c w)≠InfinitesimalSign.encode 0 ∨
        FiniteCoefficientSignScan.Zero sign (pair c w) 0 chosen) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj e he
      have hj' : j<IntegralMixedRelativeCuts.choiceIndex rule kind := by simpa only [choice_eq] using hj
      have HM:=HLower j hj'
      have HC:=congrArg (fun q : Polynomial ℝ=>q.coeff e) HM
      have HZ : φ ((IntegralMixedRelativeCuts.factor old bound rule
          (IntegralMixedRelativeCuts.atChoice rule kind j)).coeff e)=0 := by
        rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hj']
        simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
      exact (IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha HF φ hφ e j
        (by omega) (hj.le.trans HK)).mpr HZ
    · intro HZero
      have HC:=(IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha HF φ hφ degree chosen HD HK).mp HZero
      rw [self_choice] at HC
      have HT : ((factor).map φ.toRingHom).coeff degree≠0 := by
        rw [←hd]
        exact Polynomial.leadingCoeff_ne_zero.mpr HNonzero
      apply HT
      simpa only [Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
    · intro e he hgt
      have HC : ((factor).map φ.toRingHom).coeff e=0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hgt)
      apply (IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha HF φ hφ e chosen (by omega) HK).mpr
      rw [self_choice]
      simpa only [Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
    · by_cases HH : IntegralFramedTerminalCutGuards.head P D H L F C hs key hpos (pair c w)=InfinitesimalSign.encode 0
      · right
        have HZ:=(IntegralFramedTerminalCutAcceptedRoot.head_zero_iff P D H L F C hs key hpos c w hv hfit).mp HH
        have HQ:=(IntegralRelativeTruncation.jointQuotient_zero_iff (old).sampler.scalarPrefix factor degree cutTuple).mpr HZ
        have HC : φ ((factor).coeff 0)=0 := by
          simpa only [HQ,Polynomial.eval₂_at_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hroot
        apply (IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha HF φ hφ 0 chosen (Nat.zero_le _) HK).mpr
        rw [self_choice]
        exact HC
      · exact Or.inl HH
  simpa only [IntegralFramedTerminalCutGuards.Guards,FiniteCoefficientSignScan.Guards,IntegralFramedCutFiniteGuards.choice,
    IntegralFramedCutFiniteGuards.degree,IntegralFramedCutFiniteGuards.cap,pairFst_pair] using HG

end LeanCanny.Encoding.IntegralFramedTerminalCutGuardComplete
