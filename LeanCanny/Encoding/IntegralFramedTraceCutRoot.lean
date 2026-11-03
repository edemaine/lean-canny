/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutValidity
public import LeanCanny.Encoding.IntegralFramedTerminalCutRows
public import LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
public import LeanCanny.Algebra.IntegralMixedCutJointRootGuard
public import LeanCanny.Algebra.IntegralMixedCutHeadRootGuard
/-! # Datum-indexed cut guards validate roots in the actual terminal bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutRoot
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

omit hFpos hf in
include hv in
theorem exists_interpretation (ha : IntegralMixedFramedFullCutProbeBits.Active P c) (hfit : birth P c≤M) :
    ∃ φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
          (2^(G).width parent) ((G).birth parent) i := by
  have HB:=(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
  have HR : pairFst (terminal P D r)=RankedHistoryTask.root c := by
    simp only [IntegralFramedTraceCutMetadata.terminal_root,IntegralFramedTraceCutTask.task_root,pairFst_pair]
  have HRoots:=IntegralFramedCompleteSuffixSaved.parent_roots P D H c (terminal P D r) ha HR hfit z
    (IntegralFramedCompleteSuffix.terminal_roots P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv)
  obtain ⟨φ,hφ⟩:=(old).sampler.scalarPrefix.interpret ℝ (fun i=>z (i.val+(M-birth P c))) HRoots
  have HS : (G).cap parent=IntegralMixedFramedChoiceProbeSourceBits.horizon P c := by
    unfold family
    change P.cap (pairFst parent)+1=P.cap (RankedHistoryTask.root c)+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  refine ⟨φ,fun i=>?_⟩
  simpa only [HS,HB] using hφ i

omit hFpos hf in
include hv in
theorem head_zero_iff (hstage : birth P c=u.length) (hfit : birth P c<M) :
    IntegralFramedTraceCutGuards.head P D H L F C hs (pair (pair r w) u)=InfinitesimalSign.encode 0 ↔cutTuple 0=0 := by
  let idx:=M-u.length-1
  have HI : idx<(IntegralFramedTraceCutSource.input P D H L F C hs).count r := by
    change idx<M
    dsimp only [idx]
    omega
  have HHead : IntegralFramedTraceCutGuards.headIndex P D (pair (pair r w) u)=idx := by
    simp only [IntegralFramedTraceCutGuards.headIndex,IntegralFramedTraceCutGuards.count,
      IntegralFramedTraceCutGuards.root,IntegralFramedTraceCutGuards.stage,pairFst_pair,pairSnd_pair]
    dsimp only [idx]
    rw [IntegralFramedTraceCutMetadata.terminal_birth]
  have HP:=SquareSampleCompleteCoordinateSign.packet
    (IntegralFramedTraceCutSource.input P D H L F C hs) r w hv ⟨idx,HI⟩
  change SquareSampleCompleteCoordinateSign.value _ (pair (pair r w) (BinaryNatCode.encode idx))=_ at HP
  have HX : z idx=(SquareSampleCompleteVertices.candidate (IntegralFramedTraceCutSource.input P D H L F C hs) r w hv).val ⟨idx,HI⟩ := by
    change IntegralMixedFramedBankObservation.extend
      (SquareSampleCompleteVertices.candidate (IntegralFramedTraceCutSource.input P D H L F C hs) r w hv).val idx=_
    simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left HI]
  unfold IntegralFramedTraceCutGuards.head
  simp only [pairFst_pair,HHead]
  rw [HP]
  apply ((SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff).trans
  rw [←HX]
  have HD : idx=M-(birth P c+1) := by dsimp only [idx]; omega
  simp only [Fin.val_zero,Nat.zero_add,HD]

include hv in
theorem exists_root (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hcut : IntegralFramedCreatingCut.ParentCut P D c) (hstage : birth P c=u.length) (hfit : birth P c<M)
    (hg : IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (pair (pair r w) u)) :
    ∃ φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
          (2^(G).width parent) ((G).birth parent) i) ∧
      IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
      (factor).eval₂ φ.toRingHom bankPoint=0 := by
  have HB:=(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
  have HR : pairFst (terminal P D r)=RankedHistoryTask.root c := by
    simp only [IntegralFramedTraceCutMetadata.terminal_root,IntegralFramedTraceCutTask.task_root,pairFst_pair]
  have HC : IntegralFramedTerminalCutTest.count P D H (key P D) c=M := by
    change (G).birth (key P D c)=M
    rw [IntegralFramedTraceCutMetadata.key_task,pairFst_pair]
  have HF : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H (key P D) c := by rw [HB,HC]; exact hfit.le
  obtain ⟨φ,hφ⟩:=exists_interpretation P D H L F C hs r u w hv ha hfit.le
  have Hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(IntegralFramedTerminalCutTest.count P D H (key P D) c-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) (2^(G).width parent) ((G).birth parent) i := by simpa only [HC] using hφ
  obtain ⟨hvalid,hd⟩:=IntegralFramedTraceCutValidity.valid_and_degree P D H L F C hs hFpos hf r u w hv ha HF φ Hφ hg
  refine ⟨φ,hφ,hvalid,hd,?_⟩
  rw [IntegralFramedTerminalCutBankPoint.point_eq P D H c (terminal P D r) ha hcut HR hfit z]
  have HCap : (G).cap parent=IntegralMixedFramedChoiceProbeSourceBits.horizon P c := by
    unfold family
    change P.cap (pairFst parent)+1=P.cap (RankedHistoryTask.root c)+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  have Hφ' : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=cutTuple i.succ^
      UniformIntegralPowerSchedule.weights ((G).cap parent) (2^(G).width parent) ((G).birth parent) i := by
    intro i
    have HD : i.val+(M-(G).birth parent)=i.succ.val+(M-(birth P c+1)) := by simp only [Fin.val_succ]; omega
    have HI:=hφ i
    change φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^_ at HI
    rw [HD] at HI
    simpa only [HCap] using HI
  have HRoots:=IntegralFramedTerminalCutRows.prefix_roots P D H (terminal P D r) (RankedHistoryTask.root c)
    (BinaryNatCode.encode (get P .slot15 c)) (birth P c+1) HR (by omega) z
    (IntegralFramedCompleteSuffix.terminal_roots P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv)
  have HRows:=IntegralFramedCutRootRows.normalized_rows P D H c ha _ HRoots hcut
  have HD : degree≤2^(G).width parent:=((G).degree_bound parent).trans ((G).scalar_cap parent)
  have HP : (factor).map φ.toRingHom≠0:=((IntegralMixedRelativeCuts.valid_iff_lower_factors old bound rule φ kind).mp hvalid).2
  apply (IntegralRelativeTruncation.joint_root_guard (old).sampler.scalarPrefix factor degree HD φ cutTuple Hφ' HRows HP hd).mpr
  have HL : IntegralFramedTraceCutGuards.head P D H L F C hs (pair (pair r w) u)≠InfinitesimalSign.encode 0 ∨
      FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) 0
        (IntegralMixedRawKindBits.choice G parent) := by
    simpa only [IntegralFramedTraceCutGuards.choice,IntegralFramedTraceCutGuards.parent,Function.comp_apply,
      IntegralFramedTraceCutGuards.descriptor,IntegralFramedTraceCutGuards.root,pairFst_pair,pairSnd_pair] using hg.2.2.2
  rcases HL with HHead | HConstant
  · left
    intro HZero
    have HZ:=(IntegralRelativeTruncation.jointQuotient_zero_iff (old).sampler.scalarPrefix factor degree cutTuple).mp HZero
    exact HHead ((head_zero_iff P D H L F C hs r u w hv hstage hfit).mpr HZ)
  · right
    have HN:=(G).scalar_cap parent
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] at HN
    simp only [IntegralFramedTraceCutTask.task_root,pairFst_pair] at HN
    have HK : IntegralMixedRawKindBits.choice G parent≤2^P.width r:=(IntegralMixedRawKindBits.choice_le G parent).trans HN
    have HE:=(IntegralFramedTraceCutReadback.zero_iff P D H L F C hs hFpos hf r u w hv ha HF φ Hφ 0
      (IntegralMixedRawKindBits.choice G parent) (Nat.zero_le _) HK).mp HConstant
    rw [self_choice] at HE
    exact HE

end LeanCanny.Encoding.IntegralFramedTraceCutRoot
