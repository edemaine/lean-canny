/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutValidity
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan
public import LeanCanny.Encoding.IntegralFramedTraceCutOrigin

/-! # Every literal creating cut inherits its full vertex's valid factor -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralFramedTraceCutScan (stagePacket)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool) (ctx w : List Bool)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H

theorem birth_count : (G).birth ((B).key (sampleContext ctx))=
    IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer (pair ctx w) :=by
  unfold IntegralMixedPhysicalTraceCutScan.count IntegralMixedPhysicalReplayNew.count
  rw [pairFst_pair]
  rfl

variable (j : ℕ)
local notation "u" => List.replicate j true
local notation "p" => IntegralFramedPhysicalTraceCutSource.parent B (sampleContext ctx) u
local notation "old" => IntegralMixedVirtualTaskBits.saved P p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "offset" => IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old

theorem parent_stage : IntegralFramedTraceCutGuards.parent P (stagePacket (pair ctx w) j)=p :=by
  simpa only [stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,pairFst_pair,pairSnd_pair] using
    IntegralMixedPhysicalCutCoefficientSemantics.parent_packet hn ht ha hR outer ctx w u

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem origin (hj : j<IntegralFramedTraceCutMetadata.length P D ctx)
    (hcut : IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D ctx j).command) :
    IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR outer (stagePacket (pair ctx w) j) ∧
    IntegralMixedFramedFullCutProbeBits.Active P p ∧(G).birth old≤(G).birth ((B).key (sampleContext ctx)) :=by
  have HJ : j<IntegralFramedTraceCutMetadata.length P D (pairFst (pair ctx w))+1 :=by
    rw [pairFst_pair]
    omega
  have HC0 : IntegralFramedCreatingCut.IsCut
      (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (pair ctx w)) j).command :=
    Eq.mpr (congrArg (fun root=>IntegralFramedCreatingCut.IsCut
      (IntegralMixedFramedRootPullback.instructionAt P D root j).command) (pairFst_pair ctx w)) hcut
  have HC : IntegralFramedTraceCutScan.StageCut P D (stagePacket (pair ctx w) j) :=
    (IntegralFramedTraceCutOrigin.stageCut_iff P D (pair ctx w) j HJ).mpr HC0
  have HA:=IntegralFramedTraceCutOrigin.cut_active P D (pair ctx w) j HJ HC
  rw [parent_stage hn ht ha hR outer ctx w j] at HA
  have HB:=IntegralFramedTraceCutOrigin.parent_birth P D (pair ctx w) j HJ
  rw [parent_stage hn ht ha hR outer ctx w j] at HB
  have HO : (G).birth old=j :=((IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth p).trans HB
  have HM : j<IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer (pair ctx w) :=by
    rw [IntegralMixedPhysicalTraceCutScan.count_eq_length]
    exact hj
  refine ⟨HC,HA,?_⟩
  exact HO.trans_le (HM.le.trans_eq (birth_count hn ht ha hR outer ctx w).symm)

noncomputable def CoefficientCompatible
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) : Prop :=
  ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
            (2^(G).width old) ((G).birth old) i) ∧
      IntegralMixedRelativeCuts.Valid x bound rule φ kind ∧
      ((IntegralMixedRelativeCuts.factor x bound rule kind).map φ.toRingHom).natDegree=(G).degree old

theorem actual_cut
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
    (hh : IntegralMixedPhysicalTraceCutScan.holds hn ht ha hR outer (pair ctx w))
    (hj : j<IntegralFramedTraceCutMetadata.length P D ctx)
    (hcut : IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D ctx j).command) :
    CoefficientCompatible hn ht ha hR outer ctx w j hv :=by
  obtain ⟨HC,HA,HF⟩:=origin hn ht ha hR outer ctx w j hj hcut
  have HJ : j<IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer (pair ctx w) :=by
    rw [IntegralMixedPhysicalTraceCutScan.count_eq_length]
    exact hj
  have HG:=hh j HJ HC
  have HG' : IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer
      (IntegralMixedPhysicalCutCoefficientSemantics.stage ctx w u) :=by
    simpa only [stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,pairFst_pair,pairSnd_pair] using HG
  obtain ⟨φ,hφ,HGφ⟩:=IntegralMixedPhysicalCutCoefficientSemantics.exists_coefficient_guards
    hn ht ha hR outer ctx w u hv HF HA HG'
  exact ⟨φ,hφ,IntegralMixedRelativeCuts.coefficientGuards_valid _ _ _ _ _ _ HGφ,
    IntegralMixedRelativeCuts.coefficientGuards_degree _ _ _ _ _ _ HGφ⟩

theorem accepted_all (h : pair ctx w∈IntegralMixedPhysicalTraceCutScan.language hn ht ha hR outer) :
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
      ∀i<IntegralFramedTraceCutMetadata.length P D ctx,
        IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D ctx i).command→
          CoefficientCompatible hn ht ha hR outer ctx w i hv :=by
  have HP : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w ∧
      IntegralMixedPhysicalTraceCutScan.holds hn ht ha hR outer (pair ctx w) :=by
    simpa only [IntegralMixedPhysicalTraceCutScan.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using h
  exact ⟨HP.1,fun i hi hc=>actual_cut hn ht ha hR outer ctx w i HP.1 HP.2 hi hc⟩

end LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
