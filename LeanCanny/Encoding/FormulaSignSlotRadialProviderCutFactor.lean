/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutValues
public import LeanCanny.Algebra.IntegralMixedRelativeCutNativeGuards
/-! # Native provider cut guards retain the actual untruncated factor root -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderRecordPrefix (context cutParent cutSaved)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => family P D H

private theorem kind_choice (F : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice F key=IntegralMixedRelativeCuts.choiceIndex (F.rule key) (F.kind key) := by
  cases hk:F.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

private theorem factor_bank_birth (r : List Bool) : (G).birth ((B).key (context r))=
    FormulaSignSlotRadialProviderRecordPlan.fullCount r :=
  (family_birth P D H ((B).key (context r))).trans (FormulaSignSlotRadialProviderRecordPrefix.full_prefix r)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalSuffixTest.rawTuple
  FormulaSignSlotRadialProviderAtomic.Cuts.sign FormulaSignSlotRadialProviderAtomic.Cuts.head
  FormulaSignSlotRadialProviderAtomic.Cuts.Guards FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
  IntegralFramedCreatingCut.ParentCut quotient

variable (r w : List Bool)
  (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w)
  (b : ℕ) (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r)
local notation "old" => cutSaved r b
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "degree" => IntegralMixedCutSource.Family.degree G old
local notation "factor" => IntegralMixedRelativeCuts.factor x bound rule kind

include hw hb in
theorem native_guards_iff_coefficients
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Generators r w hw b φ) :
    FormulaSignSlotRadialProviderAtomic.Cuts.Guards (stage r w b) ↔
      IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind degree ∧
        (FormulaSignSlotRadialProviderAtomic.Cuts.head (stage r w b)≠InfinitesimalSign.encode 0 ∨
          φ ((factor).coeff 0)=0) := by
  have HW : (G).width old=(P).width r :=
    ((geometry P D H).width (cutParent r b)).trans (congrArg (P).width (parent_root r b))
  have HN := (G).scalar_cap old
  rw [HW] at HN
  have HK : IntegralMixedRelativeCuts.choiceIndex rule kind≤2^(P).width r :=
    (kind_choice G old).symm.trans_le ((IntegralMixedRawKindBits.choice_le G old).trans HN)
  have HD : degree≤2^(P).width r := ((G).degree_bound old).trans HN
  have HC : IntegralFramedTraceCutGuards.choice P D H (stage r w b)=
      IntegralMixedRelativeCuts.choiceIndex rule kind := by
    unfold IntegralFramedTraceCutGuards.choice
    rw [stage_parent]
    exact kind_choice G old
  have HDe : IntegralFramedTraceCutGuards.degree P D H (stage r w b)=degree := by
    unfold IntegralFramedTraceCutGuards.degree
    rw [stage_parent]
    rfl
  have HCap : IntegralFramedTraceCutGuards.cap P (stage r w b)=2^(P).width r := by
    simp only [IntegralFramedTraceCutGuards.cap,IntegralFramedTraceCutGuards.root,stage,
      IntegralFramedTraceCutScan.stagePacket,pairFst_pair]
  unfold FormulaSignSlotRadialProviderAtomic.Cuts.Guards
  exact IntegralMixedRelativeCuts.native_guards_iff x bound rule φ kind degree (2^(P).width r)
    HN HK HD FormulaSignSlotRadialProviderAtomic.Cuts.sign FormulaSignSlotRadialProviderAtomic.Cuts.head
    (IntegralFramedTraceCutGuards.choice P D H) (IntegralFramedTraceCutGuards.degree P D H)
    (IntegralFramedTraceCutGuards.cap P) (stage r w b) HC HDe HCap
    (coefficient_evaluation_at r w hw b hb φ hφ)

theorem parent_cut (hc : FormulaSignSlotRadialProviderAtomic.Cuts.StageCut (stage r w b)) :
    IntegralFramedCreatingCut.ParentCut P D (cutParent r b) := by
  unfold FormulaSignSlotRadialProviderAtomic.Cuts.StageCut IntegralFramedTraceCutScan.StageCut at hc
  have HC : IntegralFramedCreatingCut.ParentCut P D (IntegralFramedTraceCutGuards.parent P (stage r w b)) := hc
  rw [stage_parent] at HC
  exact HC

include hw hb in
theorem factor_root_iff_head
    (hc : IntegralFramedCreatingCut.ParentCut P D (cutParent r b))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Generators r w hw b φ)
    (hcg : IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind degree) :
    (factor).eval₂ φ.toRingHom (quotient r w hw b)=0 ↔
      FormulaSignSlotRadialProviderAtomic.Cuts.head (stage r w b)≠InfinitesimalSign.encode 0 ∨
        φ ((factor).coeff 0)=0 := by
  have HR : pairFst ((B).key (context r))=RankedHistoryTask.root (cutParent r b) :=
    (FormulaSignSlotRadialProviderRecordPrefix.key_root r).trans (parent_root r b).symm
  have HA := FormulaSignSlotRadialProviderRecordPrefix.cut_active r b hb
  have HF := native_fit r b hb
  have HQ := IntegralFramedTerminalCutBankPoint.point_eq P D H (cutParent r b) ((B).key (context r))
    HA hc HR HF (IntegralFramedPhysicalSuffixTest.rawTuple B (context r) w hw)
  have HL : quotient r w hw b=
      (IntegralMixedFramedBankObservation.ofState ((G).state ((B).key (context r)))).point
        (IntegralFramedPhysicalSuffixTest.rawTuple B (context r) w hw)
        ((G).birth ((B).key (context r))-birth P (cutParent r b)-1) := by
    unfold quotient
    rw [FormulaSignSlotRadialProviderRecordPrefix.cutParent_birth r b hb]
  have HQ' : quotient r w hw b=IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix factor degree
      (IntegralFramedPhysicalTraceCutSource.cutTuple B (context r) w hw (List.replicate b true)) := HL.trans HQ
  have HS : (factor).eval₂ φ.toRingHom
      (IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix factor degree
        (IntegralFramedPhysicalTraceCutSource.cutTuple B (context r) w hw (List.replicate b true)))=0 ↔
      IntegralFramedPhysicalTraceCutSource.cutTuple B (context r) w hw (List.replicate b true) 0≠0 ∨
        φ ((factor).coeff 0)=0 := IntegralFramedPhysicalTraceCutSource.factor_root_guard B
    FormulaSignSlotRadialProviderAtomic.Cuts.key_context (context r) w hw (List.replicate b true)
    HA hc HR HF φ hφ hcg
  rw [←HQ'] at HS
  have HBB : birth (B).parameters
      (IntegralFramedPhysicalTraceCutSource.parent B (context r) (List.replicate b true))=b :=
    FormulaSignSlotRadialProviderRecordPrefix.cutParent_birth r b hb
  have HBank : (family (B).parameters (B).plan (B).data).birth ((B).key (context r))=
      FormulaSignSlotRadialProviderRecordPlan.fullCount r := factor_bank_birth r
  have HZ : FormulaSignSlotRadialProviderAtomic.Cuts.head (stage r w b)=InfinitesimalSign.encode 0 ↔
      IntegralFramedPhysicalTraceCutSource.cutTuple B (context r) w hw (List.replicate b true) 0=0 := by
    simpa only [IntegralFramedPhysicalTraceCutSource.cutTuple,Fin.val_zero,Nat.zero_add,
      HBB,HBank,Nat.sub_sub] using
      head_zero_iff r w hw b hb
  exact HS.trans (or_congr (not_congr HZ).symm Iff.rfl)

include hw hb in
theorem guards_iff_factor_receipt
    (hc : IntegralFramedCreatingCut.ParentCut P D (cutParent r b)) :
    FormulaSignSlotRadialProviderAtomic.Cuts.Guards (stage r w b) ↔
      ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ, Generators r w hw b φ ∧
        IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind degree ∧
        (factor).eval₂ φ.toRingHom (quotient r w hw b)=0 := by
  constructor
  · intro hg
    obtain ⟨φ,hφ,_⟩ := coefficient_evaluation r w hw b hb
    obtain ⟨HC,HH⟩ := (native_guards_iff_coefficients r w hw b hb φ hφ).mp hg
    exact ⟨φ,hφ,HC,(factor_root_iff_head r w hw b hb hc φ hφ HC).mpr HH⟩
  · rintro ⟨φ,hφ,HC,HR⟩
    exact (native_guards_iff_coefficients r w hw b hb φ hφ).mpr
      ⟨HC,(factor_root_iff_head r w hw b hb hc φ hφ HC).mp HR⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
