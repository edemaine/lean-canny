/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutBankRoot
/-! # Exact completeness of the native finite selected-cut guards

A compatible interpretation of the same tuple, actual cut validity, the
recorded specialized degree and the actual newest bank root imply every
native guard. No algebraic coefficient is tested before specialization.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutGuardComplete
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedCutCoefficientTest.value

private theorem choice_eq (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]
private theorem self_choice (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) (IntegralMixedRawKindBits.choice G key)=G.kind key := by
  rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "model" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "oldState" => IntegralMixedCutSource.Family.state model parent
local notation "rule" => IntegralMixedCutSource.Family.rule model parent
local notation "kind" => IntegralMixedCutSource.Family.kind model parent
local notation "degree" => IntegralMixedCutSource.Family.degree model parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound model parent
local notation "factor" => IntegralMixedRelativeCuts.factor oldState bound rule kind
local notation "chosen" => IntegralMixedRawKindBits.choice model parent
local notation "sample" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv)
local notation "oldTuple" => (fun i : Fin (IntegralMixedCutSource.Family.birth model parent+1)=>
  sample (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i))
local notation "bankPoint" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state model (IntegralFramedCutSuccessor.key P c)))
  (IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv) 0
local notation "sign" => IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf

theorem guards (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (φ : (oldState).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((oldState).sampler.scalarPrefix.basis.generator i)=oldTuple i.succ^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(model).width parent) ((model).birth parent) i)
    (hvalid : IntegralMixedRelativeCuts.Valid oldState bound rule φ kind)
    (hd : ((factor).map φ.toRingHom).natDegree=degree)
    (hroot : (factor).eval₂ φ.toRingHom bankPoint=0) :
    IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w) := by
  have HN:=(model).scalar_cap parent
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
  have HK : chosen≤2^P.width (RankedHistoryTask.root c) :=
    (IntegralMixedRawKindBits.choice_le model parent).trans HN
  have HD : degree≤2^P.width (RankedHistoryTask.root c) := ((model).degree_bound parent).trans HN
  obtain ⟨HLower,HNonzero⟩:=(IntegralMixedRelativeCuts.valid_iff_lower_factors oldState bound rule φ kind).mp hvalid
  have HG :
      (∀ j<chosen,∀ e<2^P.width (RankedHistoryTask.root c)+1,FiniteCoefficientSignScan.Zero sign (pair c w) e j) ∧
      ¬FiniteCoefficientSignScan.Zero sign (pair c w) degree chosen ∧
      (∀ e<2^P.width (RankedHistoryTask.root c)+1,degree<e→FiniteCoefficientSignScan.Zero sign (pair c w) e chosen) ∧
      (IntegralFramedCutFiniteGuards.head P D H L F C hs (pair c w)≠InfinitesimalSign.encode 0 ∨
        FiniteCoefficientSignScan.Zero sign (pair c w) 0 chosen) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj e he
      have hj' : j<IntegralMixedRelativeCuts.choiceIndex rule kind := by simpa only [choice_eq] using hj
      have HM:=HLower j hj'
      have HC:=congrArg (fun q : Polynomial ℝ=>q.coeff e) HM
      have HZ : φ ((IntegralMixedRelativeCuts.factor oldState bound rule
          (IntegralMixedRelativeCuts.atChoice rule kind j)).coeff e)=0 := by
        rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hj']
        simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
      exact (IntegralFramedCutNativeValidity.zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ e j
        (by omega) (hj.le.trans HK)).mpr HZ
    · intro HZero
      have HC:=(IntegralFramedCutNativeValidity.zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ degree chosen HD HK).mp HZero
      rw [self_choice] at HC
      have HT : ((factor).map φ.toRingHom).coeff degree≠0 := by
        rw [←hd]
        exact Polynomial.leadingCoeff_ne_zero.mpr HNonzero
      apply HT
      simpa only [Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
    · intro e he hgt
      have HC : ((factor).map φ.toRingHom).coeff e=0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hgt)
      apply (IntegralFramedCutNativeValidity.zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ e chosen (by omega) HK).mpr
      rw [self_choice]
      simpa only [Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using HC
    · by_cases HH : IntegralFramedCutFiniteGuards.head P D H L F C hs (pair c w)=InfinitesimalSign.encode 0
      · right
        have HZ:=(IntegralFramedCutFiniteGuards.head_zero_iff P D H L F C hs c w hv).mp HH
        have H0 : Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) (0 : Fin ((model).birth parent+1))=
            (⟨0,IntegralFramedCutSuccessor.positive P D H c⟩ : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)) := by
          apply Fin.ext
          rfl
        have HT : oldTuple 0=0 := by
          change sample (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) 0)=0
          rw [H0]
          exact HZ
        have HQ:=(IntegralRelativeTruncation.jointQuotient_zero_iff (oldState).sampler.scalarPrefix factor degree oldTuple).mpr HT
        have HP : bankPoint=0 := (IntegralFramedCutBankRoot.point_newest P D H L F C hs c w hv ha hcut).trans HQ
        have HC : φ ((factor).coeff 0)=0 := by
          simpa only [HP,Polynomial.eval₂_at_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hroot
        apply (IntegralFramedCutNativeValidity.zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ 0 chosen (Nat.zero_le _) HK).mpr
        rw [self_choice]
        exact HC
      · exact Or.inl HH
  simpa only [IntegralFramedCutFiniteGuards.Guards,FiniteCoefficientSignScan.Guards,IntegralFramedCutFiniteGuards.choice,
    IntegralFramedCutFiniteGuards.degree,IntegralFramedCutFiniteGuards.cap,pairFst_pair] using HG

end LeanCanny.Encoding.IntegralFramedCutGuardComplete
