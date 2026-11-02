/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutAcceptedValidity
public import LeanCanny.Encoding.IntegralFramedTerminalCutRows
public import LeanCanny.Algebra.IntegralMixedCutJointRootGuard
public import LeanCanny.Algebra.IntegralMixedCutHeadRootGuard
/-! # Native terminal guards validate the full earlier cut factor root

The normalized row is the actual creating row retained inside the terminal
prefix. The zero-padding check reads that retained head. All coefficients
and the root specialize through the same literal terminal tail.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutAcceptedRoot
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedTerminalCutTest.value IntegralFramedTerminalCutGuards.head

private theorem self_choice (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) (IntegralMixedRawKindBits.choice G key)=G.kind key := by
  have HC : IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) := by
    cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]
  rw [HC,IntegralMixedRelativeCuts.atChoice_self]

private theorem extend_fin {m : ℕ} (z : Fin m→ℝ) (i : Fin m) :
    IntegralMixedFramedBankObservation.extend z i.val=z i := by
  simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt]

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

omit hFpos hf ha in
theorem head_zero_iff (hfit : birth P c<(G).birth (key c)) :
    IntegralFramedTerminalCutGuards.head P D H L F C hs key hpos (pair c w)=InfinitesimalSign.encode 0 ↔cutTuple 0=0 := by
  have HF : birth P c<IntegralFramedTerminalCutTest.count P D H key c := hfit
  have HI : IntegralFramedTerminalCutGuards.headIndex P D H key c<(IntegralFramedCompleteSquare.input P D H L F C hs key hpos).count c := by
    unfold IntegralFramedTerminalCutGuards.headIndex IntegralFramedTerminalCutTest.count
    change (G).birth (key c)-birth P c-1<(G).birth (key c)
    omega
  let i : Fin ((IntegralFramedCompleteSquare.input P D H L F C hs key hpos).count c):=⟨IntegralFramedTerminalCutGuards.headIndex P D H key c,HI⟩
  have HP:=IntegralFramedTerminalCutGuards.head_packet P D H L F C hs key hpos c w hv HF
  change IntegralFramedTerminalCutGuards.head P D H L F C hs key hpos (pair c w)=InfinitesimalSign.encode (SignType.sign (sample i)) at HP
  rw [HP]
  have HE : (InfinitesimalSign.encode (SignType.sign (sample i))=InfinitesimalSign.encode 0) ↔sample i=0 :=
    (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
  apply HE.trans
  have HX:=extend_fin sample i
  have HD : i.val=(G).birth (key c)-(birth P c+1) := by
    change IntegralFramedTerminalCutGuards.headIndex P D H key c=_
    unfold IntegralFramedTerminalCutGuards.headIndex IntegralFramedTerminalCutTest.count
    rw [Nat.sub_sub]
  change z i.val=sample i at HX
  rw [←HX,HD]
  simp only [Fin.val_zero,Nat.zero_add]

include ha in
theorem exists_root (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hroot : pairFst (key c)=RankedHistoryTask.root c) (hfit : birth P c<(G).birth (key c))
    (hg : IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w)) :
    ∃ φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=
        z (i.val+((G).birth (key c)-(G).birth parent))^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
            (2^(G).width parent) ((G).birth parent) i) ∧
      IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
      (factor).eval₂ φ.toRingHom (IntegralRelativeTruncation.jointQuotient (old).sampler.scalarPrefix factor degree cutTuple)=0 := by
  have HM : (G).birth parent=birth P c := (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
  have HF : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H key c := by
    rw [HM]
    exact hfit.le
  obtain ⟨φ,hφ,hvalid,hdegree⟩:=IntegralFramedTerminalCutAcceptedValidity.exists_valid_and_degree
    P D H L F C hs hFpos hf key hpos c w hv ha hroot HF hg
  refine ⟨φ,hφ,hvalid,hdegree,?_⟩
  have HCap : (G).cap parent=IntegralMixedFramedChoiceProbeSourceBits.horizon P c := by
    unfold family
    change P.cap (pairFst parent)+1=P.cap (RankedHistoryTask.root c)+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  have Hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=cutTuple i.succ^
      UniformIntegralPowerSchedule.weights ((G).cap parent) (2^(G).width parent) ((G).birth parent) i := by
    intro i
    have HD : i.val+((G).birth (key c)-(G).birth parent)=i.succ.val+((G).birth (key c)-(birth P c+1)) := by
      simp only [Fin.val_succ]
      omega
    have HI:=hφ i
    change φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+((G).birth (key c)-(G).birth parent))^_ at HI
    rw [HD] at HI
    simpa only [HCap] using HI
  have HRows:=IntegralFramedTerminalCutRows.rows P D H L F C hs key hpos c w hv ha hcut hroot hfit
  have HD : degree≤2^(G).width parent := ((G).degree_bound parent).trans ((G).scalar_cap parent)
  have HP : (factor).map φ.toRingHom≠0 := ((IntegralMixedRelativeCuts.valid_iff_lower_factors old bound rule φ kind).mp hvalid).2
  apply (IntegralRelativeTruncation.joint_root_guard (old).sampler.scalarPrefix factor degree HD φ cutTuple Hφ HRows HP hdegree).mpr
  have HL : IntegralFramedTerminalCutGuards.head P D H L F C hs key hpos (pair c w)≠InfinitesimalSign.encode 0 ∨
      FiniteCoefficientSignScan.Zero (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos) (pair c w) 0
        (IntegralMixedRawKindBits.choice G parent) := by
    simpa only [IntegralFramedCutFiniteGuards.choice,pairFst_pair] using hg.2.2.2
  rcases HL with HHead | HConstant
  · left
    intro HZero
    have HZ := (IntegralRelativeTruncation.jointQuotient_zero_iff (old).sampler.scalarPrefix factor degree cutTuple).mp HZero
    exact HHead ((head_zero_iff P D H L F C hs key hpos c w hv hfit).mpr HZ)
  · right
    have HN:=(G).scalar_cap parent
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
    have HK : IntegralMixedRawKindBits.choice G parent≤2^P.width (RankedHistoryTask.root c) :=
      (IntegralMixedRawKindBits.choice_le G parent).trans HN
    have HC:=(IntegralFramedTerminalCutCommonParent.zero_iff P D H L F C hs hFpos hf key hpos c w hv ha HF φ hφ 0
      (IntegralMixedRawKindBits.choice G parent) (Nat.zero_le _) HK).mp HConstant
    rw [self_choice] at HC
    exact HC

end LeanCanny.Encoding.IntegralFramedTerminalCutAcceptedRoot
