/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutAcceptedValidity
public import LeanCanny.Encoding.IntegralFramedCutNormalizedRoots
public import LeanCanny.Algebra.IntegralMixedCutHeadRootGuard
/-! # Native selected-cut guards recover a root of the actual full factor

The normalized rows come from the actual complete vertex, and the old
interpretation is constructed from its own retained tail. The final guard
removes the zero roots introduced solely by padding.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutAcceptedRoot
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedCutCoefficientTest.value

private theorem self_choice (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) (IntegralMixedRawKindBits.choice G key)=G.kind key := by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,hk,IntegralMixedRelativeCuts.atChoice,min_self]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "key" => IntegralMixedVirtualTaskBits.saved P c
local notation "x" => IntegralMixedCutSource.Family.state G key
local notation "d" => IntegralMixedCutSource.Family.degree G key
local notation "r" => IntegralMixedCutSource.Family.rule G key
local notation "k" => IntegralMixedCutSource.Family.kind G key
local notation "hm" => IntegralMixedCutSource.Family.birth_bound G key
local notation "f" => IntegralMixedRelativeCuts.factor x hm r k
local notation "z" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv)
local notation "z'" => (fun i : Fin (IntegralMixedCutSource.Family.birth G key+1)=>
  z (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i))

omit hFpos hf in
private theorem joint_cast (i : Fin ((G).birth key+1)) :
    IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv i.val=z' i := by
  have HD:=IntegralFramedCutCommonParent.dimension P D H L F C hs c ha
  have HI:=i.isLt
  have HB : i.val<(IntegralFramedCutSuccessor.input P D H L F C hs).count c := by omega
  unfold IntegralFramedCutParentInterpretation.joint IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HB]
  exact congrArg z (Fin.ext rfl)

theorem exists_root (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hg : IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w)) :
    ∃ φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ ((x).sampler.scalarPrefix.basis.generator i)=z' i.succ^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
          (2^(G).width key) ((G).birth key) i) ∧
      IntegralMixedRelativeCuts.Valid x hm r φ k ∧
      ((f).map φ.toRingHom).natDegree=d ∧
      (f).eval₂ φ.toRingHom (IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix f d z')=0 := by
  obtain ⟨φ,hφ,hvalid,hdegree⟩:=IntegralFramedCutAcceptedValidity.exists_valid_and_degree P D H L F C hs hFpos hf c w hv ha hg
  refine ⟨φ,hφ,hvalid,hdegree,?_⟩
  have HCap : (G).cap key=IntegralMixedFramedChoiceProbeSourceBits.horizon P c := by
    unfold family
    change P.cap (pairFst key)+1=P.cap (RankedHistoryTask.root c)+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  have Hφ : ∀ i,φ ((x).sampler.scalarPrefix.basis.generator i)=z' i.succ^
      UniformIntegralPowerSchedule.weights ((G).cap key) (2^(G).width key) ((G).birth key) i := by
    simpa only [HCap] using hφ
  have HF : (fun i : Fin ((G).birth key+1)=>IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv i.val)=z' :=
    funext (joint_cast P D H L F C hs c w hv ha)
  have HRows : ∀ i,(UniformIntegralPrefixRows.rows ((G).cap key) (x).sampler.scalarPrefix.rows (x).sampler.scalarPrefix.basis
      (IntegralMixedHistory.normalizedScalarPolynomial x (IntegralMixedCutMatrix.raw x hm r k d) d) d i).eval₂
        (Int.castRingHom ℝ) z'=0 := by
    intro i
    have HI:=IntegralFramedCutNormalizedRoots.rows P D H L F C hs c w hv ha hcut i
    rw [HF] at HI
    exact HI
  have HD : d≤2^(G).width key := ((G).degree_bound key).trans ((G).scalar_cap key)
  have HP : (f).map φ.toRingHom≠0 := ((IntegralMixedRelativeCuts.valid_iff_lower_factors x hm r φ k).mp hvalid).2
  apply (IntegralRelativeTruncation.joint_root_guard (x).sampler.scalarPrefix f d HD φ z' Hφ HRows HP hdegree).mpr
  have HL : IntegralFramedCutFiniteGuards.head P D H L F C hs (pair c w)≠InfinitesimalSign.encode 0 ∨
      FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w) 0
        (IntegralMixedRawKindBits.choice G key) := by
    simpa only [IntegralFramedCutFiniteGuards.choice,pairFst_pair] using hg.2.2.2
  rcases HL with HHead | HConstant
  · left
    intro HZero
    have HZ : z' 0=0 := (IntegralRelativeTruncation.jointQuotient_zero_iff (x).sampler.scalarPrefix f d z').mp HZero
    apply HHead
    apply (IntegralFramedCutFiniteGuards.head_zero_iff P D H L F C hs c w hv).mpr
    have H0 : Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) (0 : Fin ((G).birth key+1))=
        (⟨0,IntegralFramedCutSuccessor.positive P D H c⟩ : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)) := by
      apply Fin.ext
      rfl
    change z (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) 0)=0 at HZ
    rw [H0] at HZ
    exact HZ
  · right
    have HN:=(G).scalar_cap key
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
    have HK : IntegralMixedRawKindBits.choice G key≤2^P.width (RankedHistoryTask.root c) :=
      (IntegralMixedRawKindBits.choice_le G key).trans HN
    have HC:=(IntegralFramedCutNativeValidity.zero_iff P D H L F C hs hFpos hf c w hv ha φ hφ 0
      (IntegralMixedRawKindBits.choice G key) (Nat.zero_le _) HK).mp HConstant
    rw [self_choice] at HC
    exact HC

end LeanCanny.Encoding.IntegralFramedCutAcceptedRoot
