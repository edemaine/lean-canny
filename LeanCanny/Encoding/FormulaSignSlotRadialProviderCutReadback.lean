/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCutStage
public import LeanCanny.Encoding.IntegralFramedTraceCutObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalCutRootGuard
public import LeanCanny.Encoding.IntegralFramedPhysicalBankObservation
/-! # One provider own word reads its literal cut prefix and coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderRecordPrefix (context cutParent cutSaved natural observation)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "G" => family P D H

def stage (r w : List Bool) (b : ℕ) := IntegralFramedTraceCutScan.stagePacket (pair r w) b

theorem parent_root (r : List Bool) (b : ℕ) : RankedHistoryTask.root (cutParent r b)=r := by
  rw [FormulaSignSlotRadialProviderRecordPrefix.cutParent_eq,IntegralFramedTraceCutTask.task_root,pairFst_pair]

theorem stage_parent (r w : List Bool) (b : ℕ) :
    IntegralFramedTraceCutGuards.parent P (stage r w b)=cutParent r b := by
  simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root,stage,IntegralFramedTraceCutScan.stagePacket,
    FormulaSignSlotRadialProviderRecordPrefix.cutParent,IntegralFramedPhysicalTraceCutSource.parent,
    context,pairFst_pair,pairSnd_pair]
  rfl

theorem sign_packet (r w : List Bool) (b e k : ℕ) :
    FormulaSignSlotRadialProviderAtomic.Cuts.sign (FiniteCoefficientSignScan.query (stage r w b) e k)=
      IntegralFramedPhysicalTraceCutSource.value B FormulaSignSlotRadialProviderAtomic.Cuts.key_context
        FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive FormulaSignSlotRadialProviderAtomic.Cuts.fallback
        T FormulaSignSlotRadialProviderAtomic.bank_represents
        (pair (pair (context r) w) (IntegralFramedPhysicalTraceCutSource.datum (List.replicate b true) e k)) := by
  simp only [FormulaSignSlotRadialProviderAtomic.Cuts.sign,Function.comp_apply,
    FormulaSignSlotRadialProviderAtomic.Cuts.coefficientQuery,FormulaSignSlotRadialProviderAtomic.Cuts.creatingRoot,
    FormulaSignSlotRadialProviderAtomic.Cuts.ownWord,FiniteCoefficientSignScan.query,
    IntegralFramedTraceCutGuards.root,IntegralFramedTraceCutGuards.word,
    stage,IntegralFramedTraceCutScan.stagePacket,IntegralFramedPhysicalTraceCutSource.datum,context,
    pairFst_pair,pairSnd_pair]
  rfl

private theorem bank_birth (r : List Bool) : (G).birth ((B).key (context r))=
    FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
  exact (family_birth P D H ((B).key (context r))).trans (FormulaSignSlotRadialProviderRecordPrefix.full_prefix r)

theorem native_fit (r : List Bool) (b : ℕ) (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    birth P (cutParent r b)<(G).birth ((B).key (context r)) := by
  rw [FormulaSignSlotRadialProviderRecordPrefix.cutParent_birth r b hb,bank_birth]
  exact hb

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalSuffixTest.rawTuple

variable (r w : List Bool)
  (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w) (b : ℕ)
local notation "old" => cutSaved r b
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "task" => cutParent r b
local notation "offset" => IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B) task-IntegralMixedCutSource.Family.birth G old

def Generators (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop :=
  ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=IntegralFramedPhysicalSuffixTest.rawTuple B (context r) w hw
    (i.val+offset)^UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P task)
      (2^(G).width old) ((G).birth old) i

theorem coefficient_evaluation (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ, Generators r w hw b φ ∧
      ∀e k,e≤2^(P).width r→k≤2^(P).width r→
        FormulaSignSlotRadialProviderAtomic.Cuts.sign (FiniteCoefficientSignScan.query (stage r w b) e k)=
          InfinitesimalSign.encode (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x ((G).birth_bound old)
            ((G).rule old) (IntegralMixedRelativeCuts.atChoice ((G).rule old) ((G).kind old) k)).coeff e))) := by
  have HR : pairFst ((B).key (context r))=pairFst (context r) :=
    (FormulaSignSlotRadialProviderRecordPrefix.key_root r).trans (pairFst_pair r []).symm
  have HF : (G).birth old≤(G).birth ((B).key (context r)) :=
    (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth r b hb).trans_le (hb.le.trans_eq (bank_birth r).symm)
  obtain ⟨φ,hφ,HE⟩ := IntegralFramedPhysicalTraceCutSource.exists_coefficient_evaluation B
    FormulaSignSlotRadialProviderAtomic.Cuts.key_context (context r) w hw (List.replicate b true)
    FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive FormulaSignSlotRadialProviderAtomic.Cuts.fallback
    T FormulaSignSlotRadialProviderAtomic.bank_represents HR HF
    (FormulaSignSlotRadialProviderRecordPrefix.cut_active r b hb)
  refine ⟨φ,hφ,fun e k he hk=>?_⟩
  have HRoot : RankedHistoryTask.root (IntegralFramedPhysicalTraceCutSource.parent B (context r) (List.replicate b true))=r :=
    parent_root r b
  exact (sign_packet r w b e k).trans (HE e k (by rw [HRoot];exact he) (by rw [HRoot];exact hk))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
